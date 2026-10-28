-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:15:58.377188+00:00
-- url     : https://prove2.me/submissions/ff5b0225-718d-4139-a8b5-52fea04e25aa

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_finite_general_bs
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_volume_upper_of_operator_bs
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_susceptibility_upper_of_critical_operator_bs

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

variable {E : Type*}

lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFreshSelection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E ι : Type*}

lemma measure_inter_of_separate_blocks (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hdA : DependsOn (fun ω => ω ∈ A) S)
    (hdB : DependsOn (fun ω => ω ∈ B) Sᶜ) :
    law q (A ∩ B) = law q A * law q B := by
  have hBg : DependsOn (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) Sᶜ := by
    intro ω η hωη
    have h := hdB hωη
    change (ω ∈ B) = (η ∈ B) at h
    change (if ω ∈ B then (1 : ℝ≥0∞) else 0) =
      (if η ∈ B then (1 : ℝ≥0∞) else 0)
    exact congrArg (fun p : Prop => if p then (1 : ℝ≥0∞) else 0) h
  have h := lintegral_indicator_fresh q S A hA hdA
    (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) (measurable_const.indicator hB) hBg
  have heq : A.indicator (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) =
      (A ∩ B).indicator (fun _ : Set E => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [Set.indicator,ha,hb]
  have hAB : (∫⁻ ω, (A ∩ B).indicator (fun _ : Set E => (1 : ℝ≥0∞)) ω ∂law q) =
      law q (A ∩ B) := lintegral_indicator_one (hA.inter hB)
  have hB' : (∫⁻ ω, B.indicator (fun _ : Set E => (1 : ℝ≥0∞)) ω ∂law q) =
      law q B := lintegral_indicator_one hB
  rw [heq,hAB,hB'] at h
  exact h

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Basic
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}



section Deterministic
variable (G : BondGraph V E) (ω : Set E)

theorem cluster_eq_of_conn {x y : V} (h : Conn G ω x y) :
    cluster G ω x = cluster G ω y := by
  ext z
  exact ⟨fun hxz => conn_trans G ω (conn_symm G ω h) hxz,
    fun hyz => conn_trans G ω h hyz⟩

theorem conn_univ_of_connected (h : Connected G) (x y : V) : Conn G Set.univ x y := by
  apply Relation.ReflTransGen.mono (r := Adj G) ?_ x y (h x y)
  rintro a b ⟨e, he⟩
  exact ⟨e, Set.mem_univ _, he⟩

end Deterministic

section Countability


theorem countable_vertices [Nonempty V] {G : BondGraph V E}
    (hG : LocallyFinite G) (hconn : Connected G) : Countable V := by
  let x : V := Classical.arbitrary V
  have he : (Set.univ : Set V) = ⋃ n, reachBall G x n := by
    ext y
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact exists_mem_reachBall (hconn x y)
  apply Set.countable_univ_iff.mp
  rw [he]
  exact Set.countable_iUnion (fun n => (finite_reachBall hG x n).countable)

theorem countable_edges [Countable V] {G : BondGraph V E}
    (hG : LocallyFinite G) : Countable E := by
  have he : (Set.univ : Set E) = ⋃ x, {e | x ∈ G e} := by
    ext e
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨(G e).out.1, Sym2.out_fst_mem _⟩
  apply Set.countable_univ_iff.mp
  rw [he]
  exact Set.countable_iUnion (fun x => (hG x).countable)

end Countability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Bounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

section KernelLimits
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable


theorem finiteEmbedding_dense : DenseRange (finiteEmbedding (V := V)) := by
  intro f
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) f)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ y ∈ s, Finsupp.single y (f y), ?_⟩
  simp



end KernelLimits

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

 
theorem map_openEdges (p : unitInterval) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p) =
      law p := by
  unfold law
  rw [setBernoulli_eq_map]
  have hmeas : Measurable (fun labels : E → unitInterval => fun e => labels e ≤ p) :=
    Measurable.of_eval (fun e => (measurable_threshold p).comp (measurable_pi_apply e))
  have he : (fun labels : E → unitInterval => openEdges labels p) =
      (fun f : E → Prop => {e | f e}) ∘ (fun labels e => labels e ≤ p) := rfl
  rw [he, ← Measure.map_map measurable_setOfPred hmeas]
  unfold labelLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_threshold p)]
  simp only [map_threshold, Set.mem_univ, bernoulliMeasure_def]

end Coupling

section KernelDomination
attribute [local instance] Classical.propDecidable



theorem exists_operator_of_matrix_domination
    (U K : V → V → ℝ) (hU : ∀ x y, 0 ≤ U x y)
    (hKU : ∀ x y, |K x y| ≤ U x y)
    (B : Hilbert V →L[ℂ] Hilbert V)
    (hB : ∀ x y, B (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ)) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ ‖B‖ ∧
      ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (K x y : ℂ) := by
  have hcol (y : V) : Memℓp (fun x => (K x y : ℂ)) 2 := by
    apply (lp.memℓp (B (lp.single 2 y (1 : ℂ)))).mono'
    intro x
    simpa [hB x y, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU x y)]
      using hKU x y
  let col (y : V) : Hilbert V := ⟨fun x => (K x y : ℂ), hcol y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hLn (f : V →₀ ℂ) : ‖L f‖ ≤ ‖B‖ * ‖finiteEmbedding f‖ := by
    let g : V →₀ ℂ := f.mapRange (fun z => (‖z‖ : ℂ)) (by simp)
    have hg : finiteEmbedding g = positivePart (finiteEmbedding f) := by
      apply lp.ext
      funext x
      simp [g]
    have hpoint (x : V) : ‖L f x‖ ≤ ‖B (finiteEmbedding g) x‖ := by
      have hright : B (finiteEmbedding g) x =
          (∑ y ∈ f.support, ‖f y‖ * U x y : ℝ) := by
        simp only [finiteEmbedding, g, Finsupp.linearCombination_apply]
        rw [Finsupp.sum_mapRange_index (by simp)]
        simp only [Finsupp.sum, map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
          lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hB, Complex.ofReal_sum,
          Complex.ofReal_mul]
      have hnn : 0 ≤ ∑ y ∈ f.support, ‖f y‖ * U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (hU x y))
      rw [hright, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      simp only [L, Finsupp.linearCombination_apply, Finsupp.sum,
        lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      calc
        ‖∑ y ∈ f.support, f y * col y x‖ ≤
            ∑ y ∈ f.support, ‖f y * col y x‖ := norm_sum_le _ _
        _ ≤ ∑ y ∈ f.support, ‖f y‖ * U x y := by
          apply Finset.sum_le_sum
          intro y _
          simpa [col, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left (hKU x y) (norm_nonneg (f y))
    calc
      ‖L f‖ ≤ ‖B (finiteEmbedding g)‖ := lp.norm_mono (by norm_num) hpoint
      _ ≤ ‖B‖ * ‖finiteEmbedding g‖ := B.le_opNorm _
      _ = ‖B‖ * ‖finiteEmbedding f‖ := by rw [hg, norm_positivePart]
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense (norm_nonneg _) hLn, ?_⟩
  intro x y
  have h := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨‖B‖, hLn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at h
  rw [h]
  simp [L, col]

end KernelDomination

section CouplingOrder
variable [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
theorem measurable_openEdges (p : unitInterval) :
    Measurable (fun labels : E → unitInterval => openEdges labels p) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_threshold p).comp (measurable_pi_apply e)))

theorem twoPoint_eq_labelLaw (p : unitInterval) (x y : V) :
    twoPoint G p x y =
      (labelLaw {labels : E → unitInterval | Conn G (openEdges labels p) x y}).toReal := by
  unfold twoPoint
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p)
    (measurableSet_conn G x y)]
  rfl

omit [Countable E] in
theorem openEdges_mono (labels : E → unitInterval) : Monotone (openEdges labels) := by
  intro p q hpq e he
  exact he.trans hpq

theorem twoPoint_mono (x y : V) : Monotone (fun p => twoPoint G p x y) := by
  intro p q hpq
  change twoPoint G p x y ≤ twoPoint G q x y
  rw [twoPoint_eq_labelLaw, twoPoint_eq_labelLaw]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro labels h
  exact conn_mono G (openEdges_mono labels hpq) h

end CouplingOrder

section NormOrder
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E] (G : BondGraph V E)

theorem operatorBounded_of_le {p q : unitInterval} (hpq : p ≤ q)
    (hq : OperatorBounded G q) : OperatorBounded G p := by
  obtain ⟨B, hB⟩ := hq
  obtain ⟨A, _, hA⟩ := exists_operator_of_matrix_domination
    (twoPoint G q) (twoPoint G p) (twoPoint_nonneg G q)
    (fun x y => (abs_of_nonneg (twoPoint_nonneg G p x y)).le.trans
      (twoPoint_mono G x y hpq)) B hB
  exact ⟨A, hA⟩

end NormOrder

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

section FiniteAssociation
attribute [local instance] Classical.propDecidable
variable [Fintype E]

private theorem bernoulli_atom_product (p : unitInterval) (ω : Set E) :
    (law p).real {ω} = ∏ e : E, if e ∈ ω then (p : ℝ) else 1 - p := by
  rw [law, setBernoulli_real_singleton p (Set.subset_univ ω) (Set.finite_univ)]
  simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.sdiff_eq]
  exact Or.inl rfl

private theorem bernoulli_atom_modular (p : unitInterval) (a b : Set E) :
    (law p).real {a} * (law p).real {b} =
      (law p).real {a ∩ b} * (law p).real {a ∪ b} := by
  simp only [bernoulli_atom_product, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases ha : e ∈ a <;> by_cases hb : e ∈ b <;> simp [ha, hb, mul_comm]

 

theorem association_finite (p : unitInterval) (f g : Set E → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f ω ∂law p) * (∫ ω, g ω ∂law p) ≤ ∫ ω, f ω * g ω ∂law p := by
  have h := fkg f g (fun ω : Set E => (law p).real {ω})
    (fun _ => measureReal_nonneg) hf0 hg0 hf hg
    (fun a b => (bernoulli_atom_modular p a b).le)
  have hsum : (∑ ω : Set E, (law p).real {ω}) = 1 := by
    simp
  rw [hsum, one_mul] at h
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul] using h

 
theorem association_events_finite (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real A * (law p).real B ≤ (law p).real (A ∩ B) := by
  have hm (S : Set (Set E)) (hS : IsUpperSet S) :
      Monotone (S.indicator (fun _ => (1 : ℝ))) := by
    intro a b hab
    by_cases ha : a ∈ S
    · simp [ha, hS hab ha]
    · simp only [Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have he : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
      B.indicator (fun _ => (1 : ℝ)) ω) = (A ∩ B).indicator (fun _ => 1) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha, hb]
  have h := association_finite p _ _ (hm A hA) (hm B hB)
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
  rw [he] at h
  simpa only [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet B),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet (A ∩ B)),
    smul_eq_mul, mul_one] using h

end FiniteAssociation

section Restriction

theorem measurable_set_restrict (s : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply e.val).comp MeasurableEquiv.setOfPred.symm.measurable))

 
theorem law_map_restrict (p : unitInterval) (s : Set E) :
    (law p : Measure (Set E)).map (fun ω => (Subtype.val ⁻¹' ω : Set s)) = law p := by
  have hm := measurable_set_restrict s
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ∘
      (fun f : E → Prop => {e | f e}) =
      (fun f : s → Prop => {e | f e}) ∘ s.domRestrict := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop),
    Measure.infinitePi_map_restrict', setBernoulli_eq_map]
  simp only [Set.mem_univ]

end Restriction

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology


theorem association_restricted (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A ∩ B} := by
  let A' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ A}
  let B' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ B}
  have hA' : IsUpperSet A' := fun _ _ h ha => hA (Set.image_mono h) ha
  have hB' : IsUpperSet B' := fun _ _ h hb => hB (Set.image_mono h) hb
  have he (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) =
      ω ∩ (s : Set E) := by
    ext e
    simp [and_comm]
  have hl (C : Set (Set E)) :
      (law p : Measure (Set (s : Set E))).real {η | Subtype.val '' η ∈ C} =
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} := by
    rw [← law_map_restrict p (s : Set E), measureReal_def,
      Measure.map_apply (measurable_set_restrict _) .of_discrete]
    simp only [Set.preimage_ofPred_eq, he, measureReal_def]
  have ht := association_events_finite p A' B' hA' hB'
  change (law p).real {η | Subtype.val '' η ∈ A} *
    (law p).real {η | Subtype.val '' η ∈ B} ≤
    (law p).real {η | Subtype.val '' η ∈ A ∩ B} at ht
  simpa only [hl] using ht

 theorem edgeExhaustion_mono [Encodable E] :
    Monotone (edgeExhaustion : ℕ → Finset E) := by
  intro m n h e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range] at he ⊢
  exact he.trans_le h

private theorem subset_edgeExhaustion [Encodable E] (s : Finset E) :
    ∃ n, s ⊆ edgeExhaustion n := by
  refine ⟨s.sup Encodable.encode + 1, ?_⟩
  intro e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup he)

 theorem witness_eq_union [Encodable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hf : FiniteWitness A) :
    A = ⋃ n, {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hω
    obtain ⟨s, hs, hsa⟩ := hf ω hω
    obtain ⟨n, hn⟩ := subset_edgeExhaustion s
    exact ⟨n, hA (fun _ he => ⟨hs he, hn he⟩) hsa⟩
  · rintro ⟨n, hn⟩
    exact hA Set.inter_subset_left hn

 

theorem association_finiteWitness [Countable E] (p : unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real A * (law p).real B ≤ (law p).real (A ∩ B) := by
  let := Encodable.ofCountable E
  have hfAB : FiniteWitness (A ∩ B) := by
    intro ω hω
    obtain ⟨s, hs, hsa⟩ := hfA ω hω.1
    obtain ⟨t, ht, htb⟩ := hfB ω hω.2
    refine ⟨s ∪ t, ?_, hA ?_ hsa, hB ?_ htb⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs ht
    · simp only [Finset.coe_union]; exact Set.subset_union_left
    · simp only [Finset.coe_union]; exact Set.subset_union_right
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto
    ((hlim A hA hfA).mul (hlim B hB hfB)) (hlim (A ∩ B) (hA.inter hB) hfAB)
    (Filter.Eventually.of_forall fun n => association_restricted p A B hA hB (edgeExhaustion n))

end WitnessAssociation

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hfA : FiniteWitness A) : MeasurableSet A := by
  let := Encodable.ofCountable E
  rw [witness_eq_union A hA hfA]
  apply MeasurableSet.iUnion
  intro n
  let s := edgeExhaustion (E := E) n
  have he : {ω : Set E | ω ∩ (s : Set E) ∈ A} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ A} := by
    ext ω
    change ω ∩ (s : Set E) ∈ A ↔ Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) ∈ A
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) = ω ∩ (s : Set E) := by
      ext e
      simp [and_comm]
    rw [hi]
  change MeasurableSet {ω : Set E | ω ∩ (s : Set E) ∈ A}
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

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

theorem finiteWitness_conn_finset (G : BondGraph V E) (x : V) (t : Finset V) :
    FiniteWitness {ω | ∀ y ∈ t, Conn G ω x y} := by
  intro ω h
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert a t ha ih =>
    obtain ⟨s, hs, hsa⟩ := finiteWitness_conn G x a ω (h a (by simp))
    obtain ⟨r, hr, hrt⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨s ∪ r, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs hr
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact conn_mono G (by simp) hsa
      · exact conn_mono G (by simp) (hrt y hy)


theorem clusterLarge_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (clusterLarge G x n) := by
  rintro ω η h ⟨t, ht, hc⟩
  exact ⟨t, ht, fun y hy => conn_mono G h (hc y hy)⟩

theorem finiteWitness_clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (clusterLarge G x n) := by
  rintro ω ⟨t, ht, hc⟩
  obtain ⟨s, hs, hsc⟩ := finiteWitness_conn_finset G x t ω hc
  exact ⟨s, hs, t, ht, hsc⟩

theorem measurableSet_clusterLarge [Countable E] (G : BondGraph V E) (x : V) (n : ℕ) :
    MeasurableSet (clusterLarge G x n) :=
  measurableSet_finiteWitness _ (clusterLarge_upper G x n) (finiteWitness_clusterLarge G x n)

theorem clusterLarge_antitone (G : BondGraph V E) (x : V) :
    Antitone (clusterLarge G x) := by
  rintro m n h ω ⟨t, ht, hc⟩
  exact ⟨t, h.trans ht, hc⟩

theorem infinite_cluster_eq_iInter (G : BondGraph V E) (x : V) :
    {ω | (cluster G ω x).Infinite} = ⋂ n, clusterLarge G x n := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h n
    obtain ⟨t, ht, hcard⟩ := h.exists_subset_card_eq n
    exact ⟨t, hcard.ge, ht⟩
  · intro h hfin
    obtain ⟨t, ht, hc⟩ := h (hfin.toFinset.card + 1)
    have hsub : t ⊆ hfin.toFinset := fun y hy => hfin.mem_toFinset.mpr (hc y hy)
    have := Finset.card_le_card hsub
    omega

theorem measurableSet_infinite_cluster [Countable E] (G : BondGraph V E) (x : V) :
    MeasurableSet {ω | (cluster G ω x).Infinite} := by
  rw [infinite_cluster_eq_iInter]
  exact MeasurableSet.iInter (measurableSet_clusterLarge G x)

 
theorem association_decreasing [Countable E] (p : unitInterval)
    (A B : ℕ → Set (Set E)) (hA : Antitone A) (hB : Antitone B)
    (huA : ∀ n, IsUpperSet (A n)) (huB : ∀ n, IsUpperSet (B n))
    (hfA : ∀ n, FiniteWitness (A n)) (hfB : ∀ n, FiniteWitness (B n)) :
    (law p).real (⋂ n, A n) * (law p).real (⋂ n, B n) ≤
      (law p).real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
  have hlim (C : ℕ → Set (Set E)) (hm : Antitone C) (hC : ∀ n, MeasurableSet (C n)) :
      Tendsto (fun n => (law p).real (C n)) atTop (𝓝 ((law p).real (⋂ n, C n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_measure_iInter_atTop (fun n => (hC n).nullMeasurableSet) hm
        ⟨0, measure_ne_top _ _⟩)
  have hmA n := measurableSet_finiteWitness (A n) (huA n) (hfA n)
  have hmB n := measurableSet_finiteWitness (B n) (huB n) (hfB n)
  have h := le_of_tendsto_of_tendsto ((hlim A hA hmA).mul (hlim B hB hmB))
    (hlim (fun n => A n ∩ B n) (fun m n h => Set.inter_subset_inter (hA h) (hB h))
      (fun n => (hmA n).inter (hmB n)))
    (Filter.Eventually.of_forall fun n =>
      association_finiteWitness p (A n) (B n) (huA n) (huB n) (hfA n) (hfB n))
  simpa only [Set.iInter_inter_distrib] using h



end ClusterEvents

section Automorphisms
attribute [local instance] Classical.propDecidable

theorem infinite_cluster_aut [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x : V) :
    (law p).real {ω | (cluster G ω (a x)).Infinite} =
      (law p).real {ω | (cluster G ω x).Infinite} := by
  have he : {ω | (cluster G ω (a x)).Infinite} =
      (fun ω => b ⁻¹' ω) ⁻¹' {ω | (cluster G ω x).Infinite} := by
    ext ω
    change (cluster G ω (a x)).Infinite ↔ (cluster G (b ⁻¹' ω) x).Infinite
    rw [← cluster_aut G h]
    exact Set.infinite_image_iff (fun _ _ _ _ hab => a.injective hab)
  unfold Measure.real
  rw [he, ← Measure.map_apply (measurable_set_preimage b)
    (measurableSet_infinite_cluster G x), law_map_preimage_equiv]

 
theorem finite_open_probability (p : unitInterval) (s : Finset E) :
    (law p).real {ω | (s : Set E) ⊆ ω} = (p : ℝ) ^ s.card := by
  have he : {ω : Set E | (s : Set E) ⊆ ω} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹' {Set.univ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => Set.eq_univ_of_forall fun e => h e.property,
      fun h e he => show (⟨e, he⟩ : (s : Set E)) ∈ (Subtype.val ⁻¹' ω) from
        h.symm ▸ Set.mem_univ _⟩
  unfold Measure.real
  rw [he, ← Measure.map_apply (measurable_set_restrict _) (by measurability),
    law_map_restrict]
  change (law p : Measure (Set (s : Set E))).real {Set.univ} = _
  simp [law, setBernoulli_real_singleton p (Set.Subset.refl _) (Set.toFinite _)]

theorem twoPoint_pos [Countable E] (G : BondGraph V E) (hG : Connected G)
    (p : unitInterval) (hp : 0 < p) (x y : V) : 0 < twoPoint G p x y := by
  obtain ⟨s, _, hs⟩ := finiteWitness_conn G x y Set.univ (conn_univ_of_connected G hG x y)
  have hpos : 0 < (law p).real {ω | (s : Set E) ⊆ ω} := by
    rw [finite_open_probability]
    exact pow_pos hp _
  apply lt_of_lt_of_le hpos
  exact measureReal_mono (fun _ hω => conn_mono G hω hs)

end Automorphisms

section UniquenessThreshold
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] in
 
theorem association_infinite_conn (G : BondGraph V E) (p : unitInterval) (x y z : V) :
    (law p).real {ω | (cluster G ω x).Infinite} * twoPoint G p y z ≤
      (law p).real {ω | (cluster G ω x).Infinite ∧ Conn G ω y z} := by
  have h := association_decreasing p (clusterLarge G x) (fun _ => {ω | Conn G ω y z})
    (clusterLarge_antitone G x) antitone_const (clusterLarge_upper G x)
    (fun _ _ _ hsub hconn => conn_mono G hsub hconn) (finiteWitness_clusterLarge G x)
    (fun _ => finiteWitness_conn G y z)
  simpa only [← infinite_cluster_eq_iInter, Set.iInter_const, twoPoint, Measure.real, Set.inter_def, Set.mem_ofPred_eq] using h

end UniquenessThreshold

section DisjointWitness
attribute [local instance] Classical.propDecidable


theorem disjointOccurrence_upper (A B : Set (Set E)) : IsUpperSet (DisjointOccurrence A B) := by
  rintro ω η h ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs.trans h, ht.trans h, hd, ha, hb⟩

theorem finiteWitness_disjointOccurrence (A B : Set (Set E)) :
    FiniteWitness (DisjointOccurrence A B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  refine ⟨s ∪ t, ?_, s, t, ?_, ?_, hd, ha, hb⟩
  · simpa only [Finset.coe_union] using Set.union_subset hs ht
  · simp
  · simp

theorem disjointOccurrence_mono {A A' B B' : Set (Set E)}
    (hA : A ⊆ A') (hB : B ⊆ B') : DisjointOccurrence A B ⊆ DisjointOccurrence A' B' := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs, ht, hd, hA ha, hB hb⟩


theorem openSection_upper {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    IsUpperSet (openSection A e) :=
  fun _ _ h hω => hA (Set.insert_subset_insert h) hω

theorem subset_openSection {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    A ⊆ openSection A e := fun ω hω => hA (Set.subset_insert e ω) hω

 
theorem openSection_disjointOccurrence (A B : Set (Set E)) (_hA : IsUpperSet A)
    (hB : IsUpperSet B) (e : E) :
    openSection (DisjointOccurrence A B) e ⊆
      DisjointOccurrence (openSection A e) B ∪ DisjointOccurrence A (openSection B e) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  by_cases he : e ∈ s
  · left
    have het : e ∉ t := fun h => Finset.disjoint_left.mp hd he h
    refine ⟨s.erase e, t, ?_, ?_, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd, ?_, hb⟩
    · intro z hz
      exact (hs (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · intro z hz
      rcases ht hz with rfl | hz'
      · exact (het hz).elim
      · exact hz'
    · change insert e (↑(s.erase e) : Set E) ∈ A
      simpa only [← Finset.coe_insert, Finset.insert_erase he] using ha
  · right
    refine ⟨s, t.erase e, ?_, ?_, Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd, ha, ?_⟩
    · intro z hz
      rcases hs hz with rfl | hz'
      · exact (he hz).elim
      · exact hz'
    · intro z hz
      exact (ht (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · apply hB ?_ hb
      intro z hz
      by_cases hze : z = e
      · exact Or.inl hze
      · exact Or.inr (Finset.mem_erase.mpr ⟨hze, hz⟩)



theorem finiteProbability_mono (p : unitInterval) (s : Finset E)
    {A B : Set (Set E)} (h : A ⊆ B) : finiteProbability p s A ≤ finiteProbability p s B := by
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ha hb hb
  · exact le_rfl
  · exact (hb (h ha)).elim
  · exact mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  · exact le_rfl

theorem finiteProbability_union_add_inter (p : unitInterval) (s : Finset E)
    (A B : Set (Set E)) :
    finiteProbability p s (A ∪ B) + finiteProbability p s (A ∩ B) =
      finiteProbability p s A + finiteProbability p s B := by
  simp only [finiteProbability, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ha : (t : Set E) ∈ A <;> by_cases hb : (t : Set E) ∈ B <;> simp [ha, hb]

theorem finiteProbability_insert (p : unitInterval) (s : Finset E) (e : E) (he : e ∉ s)
    (A : Set (Set E)) :
    finiteProbability p (insert e s) A =
      (1 - p : ℝ) * finiteProbability p s A + (p : ℝ) * finiteProbability p s (openSection A e) := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  simp only [finiteProbability, Finset.powerset_insert, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum, Finset.card_insert_of_notMem he]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp ht)
    have hexp : s.card + 1 - t.card = (s.card - t.card) + 1 := by omega
    rw [hexp, pow_succ]
    split_ifs <;> simp_all [mul_comm, mul_left_comm]
  · apply Finset.sum_congr rfl
    intro t ht
    have het : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    simp only [Finset.card_insert_of_notMem het, Nat.add_sub_add_right, pow_succ,
      Finset.coe_insert, openSection, Set.mem_ofPred_eq]
    split_ifs <;> simp_all [mul_assoc, mul_comm]

end DisjointWitness

section FiniteBK
attribute [local instance] Classical.propDecidable



theorem finiteProbability_disjointOccurrence_le_half (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (s : Finset E) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteProbability p s (DisjointOccurrence A B) ≤
      finiteProbability p s A * finiteProbability p s B := by
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    simp only [finiteProbability_empty, empty_mem_disjointOccurrence]
    by_cases ha : (∅ : Set E) ∈ A <;> by_cases hb : (∅ : Set E) ∈ B <;> simp [ha, hb]
  | @insert e s he ih =>
    let A1 := openSection A e
    let B1 := openSection B e
    let D00 := DisjointOccurrence A B
    let D10 := DisjointOccurrence A1 B
    let D01 := DisjointOccurrence A B1
    have hD : D00 ⊆ D10 ∩ D01 := by
      intro ω hω
      exact ⟨disjointOccurrence_mono (subset_openSection hA e) (Set.Subset.refl _) hω,
        disjointOccurrence_mono (Set.Subset.refl _) (subset_openSection hB e) hω⟩
    have hsec : finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s D10 + finiteProbability p s D01 - finiteProbability p s D00 := by
      have h1 := finiteProbability_mono p s (openSection_disjointOccurrence A B hA hB e)
      have h2 := finiteProbability_mono p s hD
      have h3 := finiteProbability_union_add_inter p s D10 D01
      change finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s (D10 ∪ D01) at h1
      linarith
    have h00 := ih A B hA hB
    have h10 := ih A1 B (openSection_upper hA e) hB
    have h01 := ih A B1 hA (openSection_upper hB e)
    have ha := finiteProbability_mono p s (subset_openSection hA e)
    have hb := finiteProbability_mono p s (subset_openSection hB e)
    have hcoef : 0 ≤ 1 - 2 * (p : ℝ) := by linarith
    have hdif : 0 ≤ ((p : ℝ) ^ 2) *
        (finiteProbability p s A1 - finiteProbability p s A) *
        (finiteProbability p s B1 - finiteProbability p s B) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ha)) (sub_nonneg.mpr hb)
    rw [finiteProbability_insert p s e he, finiteProbability_insert p s e he,
      finiteProbability_insert p s e he]
    have hm := mul_le_mul_of_nonneg_left hsec p.2.1
    have hm00 := mul_le_mul_of_nonneg_left h00 hcoef
    have hm10 := mul_le_mul_of_nonneg_left h10 p.2.1
    have hm01 := mul_le_mul_of_nonneg_left h01 p.2.1
    change (1 - (p : ℝ)) * finiteProbability p s D00 +
      (p : ℝ) * finiteProbability p s (openSection D00 e) ≤
      ((1 - (p : ℝ)) * finiteProbability p s A + (p : ℝ) * finiteProbability p s A1) *
      ((1 - (p : ℝ)) * finiteProbability p s B + (p : ℝ) * finiteProbability p s B1)
    nlinarith

end FiniteBK

section BKMeasure
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem finiteProbability_univ [Fintype E] (p : unitInterval) (A : Set (Set E)) :
    finiteProbability p Finset.univ A = (law p).real A := by
  have he : (law p).real A = ∑ ω : Set E, if ω ∈ A then (law p).real {ω} else 0 := by
    have h := integral_fintype (μ := law p) (f := A.indicator (fun _ => (1 : ℝ)))
      Integrable.of_finite
    rw [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A)] at h
    simpa [smul_eq_mul, mul_ite, Set.indicator_apply] using h
  rw [he, finiteProbability]
  apply Finset.sum_bij (fun (t : Finset E) _ => (t : Set E))
  · simp
  · intro a _ b _ h
    exact Finset.coe_injective h
  · intro ω _
    exact ⟨ω.toFinset, by simp, by simp⟩
  · intro t _
    rw [law, setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ]
    simp [Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card]

theorem disjointOccurrence_image {F : Type*} (f : F ↪ E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B =
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  ext ω
  constructor
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    let s' := s.preimage f f.injective.injOn
    let t' := t.preimage f f.injective.injOn
    have hs' : (s' : Set F) = f ⁻¹' (s : Set E) := by simp [s']
    have ht' : (t' : Set F) = f ⁻¹' (t : Set E) := by simp [t']
    have hsI : f '' (s' : Set F) = (s : Set E) := by
      rw [hs', Set.image_preimage_eq_of_subset]
      exact hs.trans (Set.image_subset_range _ _)
    have htI : f '' (t' : Set F) = (t : Set E) := by
      rw [ht', Set.image_preimage_eq_of_subset]
      exact ht.trans (Set.image_subset_range _ _)
    refine ⟨s', t', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs']
      exact (Set.preimage_mono hs).trans (by rw [Set.preimage_image_eq _ f.injective])
    · rw [ht']
      exact (Set.preimage_mono ht).trans (by rw [Set.preimage_image_eq _ f.injective])
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      exact Finset.disjoint_left.mp hd (by simpa [s'] using hx) (by simpa [t'] using hy)
    · change f '' (s' : Set F) ∈ A
      rwa [hsI]
    · change f '' (t' : Set F) ∈ B
      rwa [htI]
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    refine ⟨s.map f, t.map f, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_map] using Set.image_mono hs
    · simpa only [Finset.coe_map] using Set.image_mono ht
    · exact (Finset.disjoint_map f).mpr hd
    · simpa only [Finset.coe_map, Set.mem_preimage] using ha
    · simpa only [Finset.coe_map, Set.mem_preimage] using hb

theorem bk_finite_half [Fintype E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  simpa only [finiteProbability_univ] using
    finiteProbability_disjointOccurrence_le_half p hp Finset.univ A B hA hB

theorem bk_restricted_half (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ DisjointOccurrence A B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} := by
  let f : (s : Set E) ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  have hreal (C : Set (Set E)) :
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} =
        (law p).real {η : Set (s : Set E) | f '' η ∈ C} := by
    rw [← law_map_restrict p (s : Set E)]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_set_restrict _) MeasurableSet.of_discrete]
    congr 2
    ext ω
    change ω ∩ (s : Set E) ∈ C ↔ f '' (Subtype.val ⁻¹' ω) ∈ C
    have he : f '' (Subtype.val ⁻¹' ω) = ω ∩ (s : Set E) := by
      ext e
      simp [f, and_comm]
    rw [he]
  rw [hreal, hreal, hreal]
  have hh := bk_finite_half p hp ((fun ω => f '' ω) ⁻¹' A)
    ((fun ω => f '' ω) ⁻¹' B)
    (fun _ _ h hω => hA (Set.image_mono h) hω)
    (fun _ _ h hω => hB (Set.image_mono h) hω)
  rw [← disjointOccurrence_image] at hh
  exact hh

 
theorem bk_finiteWitness_half [Countable E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  let := Encodable.ofCountable E
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  apply le_of_tendsto_of_tendsto
    (hlim _ (disjointOccurrence_upper A B) (finiteWitness_disjointOccurrence A B))
    ((hlim A hA hfA).mul (hlim B hB hfB))
  exact Filter.Eventually.of_forall fun n => bk_restricted_half p hp A B hA hB (edgeExhaustion n)

end BKMeasure

section ORLift
attribute [local instance] Classical.propDecidable

instance bitLaw_isProbabilityMeasure (q : unitInterval) : IsProbabilityMeasure (bitLaw q) := by
  rw [bitLaw, ← map_threshold q]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

 
theorem map_nonempty (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set F)).map Set.Nonempty = bitLaw (orParameter q (Fintype.card F)) := by
  let μ := (law q : Measure (Set F)).map Set.Nonempty
  have hm : Measurable (Set.Nonempty : Set F → Prop) := .of_discrete
  have : IsProbabilityMeasure μ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hfalse : μ.real {False} = (1 - (q : ℝ)) ^ Fintype.card F := by
    change ((law q).map Set.Nonempty).real {False} = _
    simp only [Measure.real, Measure.map_apply hm (measurableSet_singleton _)]
    have he : Set.Nonempty ⁻¹' ({False} : Set Prop) = ({∅} : Set (Set F)) := by
      ext ω
      simp [Set.not_nonempty_iff_eq_empty]
    rw [he]
    change (law q).real {∅} = _
    rw [law, setBernoulli_real_singleton q (Set.empty_subset _) Set.finite_univ]
    simp [Set.ncard_univ, Nat.card_eq_fintype_card]
  have htrue : μ.real {True} = 1 - (1 - (q : ℝ)) ^ Fintype.card F := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext b; simp
    rw [he, measureReal_compl (measurableSet_singleton _), probReal_univ, hfalse]
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (orParameter q (Fintype.card F))).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [htrue]
    simp [bitLaw, Measure.real, orParameter]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hfalse]
    simp [bitLaw, Measure.real, orParameter]

 
theorem finite_image_lift {F : Type*} (f : F → E) {ω : Set F} (s : Finset E)
    (hs : (s : Set E) ⊆ f '' ω) :
    ∃ t : Finset F, (t : Set F) ⊆ ω ∧ f '' (t : Set F) = (s : Set E) := by
  have hex : ∃ t ⊆ f '' ω, t.Finite ∧ t = (s : Set E) :=
    ⟨s, hs, s.finite_toSet, rfl⟩
  obtain ⟨t, ht, htf, hti⟩ := Set.exists_subset_image_finite_and.mp hex
  exact ⟨htf.toFinset, by simpa using ht, by simpa using hti⟩

theorem finiteWitness_image_preimage {F : Type*} (f : F → E) (A : Set (Set E))
    (hA : FiniteWitness A) : FiniteWitness ((fun ω => f '' ω) ⁻¹' A) := by
  intro ω hω
  obtain ⟨s, hs, ha⟩ := hA (f '' ω) hω
  obtain ⟨t, ht, htI⟩ := finite_image_lift f s hs
  exact ⟨t, ht, by simpa only [Set.mem_preimage, htI] using ha⟩

theorem image_preimage_disjointOccurrence {F : Type*} (f : F → E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B ⊆
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  obtain ⟨s', hs', hsI⟩ := finite_image_lift f s hs
  obtain ⟨t', ht', htI⟩ := finite_image_lift f t ht
  refine ⟨s', t', hs', ht', ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxs : f x ∈ (s : Set E) := hsI ▸ Set.mem_image_of_mem f hx
    have hxt : f x ∈ (t : Set E) := htI ▸ Set.mem_image_of_mem f hy
    exact Finset.disjoint_left.mp hd hxs hxt
  · simpa only [Set.mem_preimage, hsI] using ha
  · simpa only [Set.mem_preimage, htI] using hb

end ORLift

section ORLaw
attribute [local instance] Classical.propDecidable

theorem map_exists_bitLaw (q : unitInterval) (F : Type*) [Fintype F] :
    (Measure.infinitePi (fun _ : F => bitLaw q)).map (fun f : F → Prop => ∃ j, f j) =
      bitLaw (orParameter q (Fintype.card F)) := by
  have h := map_nonempty q F
  unfold law at h
  rw [setBernoulli_eq_map, Measure.map_map (Measurable.of_discrete) measurable_setOfPred] at h
  simpa only [Set.mem_univ, Function.comp_def, Set.Nonempty, Set.mem_ofPred_eq,
    bernoulliMeasure_def, bitLaw] using h

theorem measurable_image_fst (F : Type*) [Fintype F] :
    Measurable (fun ω : Set (E × F) => Prod.fst '' ω) := by
  have hm : Measurable (fun ω : Set (E × F) => fun e => ∃ j : F, (e,j) ∈ ω) := by
    apply Measurable.of_eval
    intro e
    apply measurableSet_setOfPred.mp
    have he : {ω : Set (E × F) | ∃ j : F, (e,j) ∈ ω} =
        ⋃ j : F, {ω : Set (E × F) | (e,j) ∈ ω} := by ext ω; simp
    rw [he]
    exact MeasurableSet.iUnion fun j => measurableSet_setOfPred.mpr
      ((measurable_pi_apply (e,j)).comp MeasurableEquiv.setOfPred.symm.measurable)
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) =
      (fun f : E → Prop => {e | f e}) ∘ (fun ω e => ∃ j : F, (e,j) ∈ ω) := by
    funext ω
    ext e
    simp [Prod.exists]
  rw [he]
  exact measurable_setOfPred.comp hm

 
theorem law_map_image_fst (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set (E × F))).map (fun ω => Prod.fst '' ω) =
      law (orParameter q (Fintype.card F)) := by
  let c := MeasurableEquiv.curry E F Prop
  let b := fun f : E → F → Prop => fun e => ∃ j, f e j
  have hb : Measurable b := Measurable.of_eval
    (fun e => (Measurable.of_discrete : Measurable (fun f : F → Prop => ∃j, f j)).comp
      (measurable_pi_apply e))
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map (measurable_image_fst F) measurable_setOfPred]
  simp only [Set.mem_univ]
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) ∘ (fun f => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘ b ∘ c := by
    funext f
    ext e
    simp [b, c, Function.comp_def, Prod.exists]
  rw [he, ← Measure.map_map measurable_setOfPred (hb.comp c.measurable),
    ← Measure.map_map hb c.measurable]
  change ((Measure.infinitePi (fun _ : E × F => bitLaw q)).map c |>.map b |>.map
    (fun f : E → Prop => {e | f e})) = _
  rw [Measure.infinitePi_map_curry (fun (_ : E) (_ : F) => bitLaw q)]
  dsimp only [b]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  rw [map_exists_bitLaw q F]
  rw [setBernoulli_eq_map]
  rfl

 
theorem exists_orParameter (p : unitInterval) (hp : p < 1) :
    ∃ m : ℕ, ∃ q : unitInterval, (q : ℝ) ≤ 1 / 2 ∧ orParameter q m = p := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - (p : ℝ) by exact sub_pos.mpr hp)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let f := fun x : ℝ => 1 - (1-x)^m
  have hf : Continuous f := by fun_prop
  have h0 : f 0 = 0 := by simp [f]
  have hp' : (p : ℝ) ∈ Set.Icc (f 0) (f (1/2)) := by
    rw [h0]
    refine ⟨p.2.1, ?_⟩
    dsimp [f]
    norm_num at hm ⊢
    linarith
  obtain ⟨q, hq, hqp⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1/2)
    hf.continuousOn hp'
  refine ⟨m, ⟨q, hq.1, hq.2.trans (by norm_num)⟩, hq.2, ?_⟩
  apply Subtype.ext
  exact hqp

end ORLaw

section BK
attribute [local instance] Classical.propDecidable

theorem disjointOccurrence_subset_inter (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) : DisjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨s,t,hs,ht,_,ha,hb⟩
  exact ⟨hA hs ha, hB ht hb⟩

 

theorem bk [Countable E] (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  by_cases hp : p = 1
  · subst p
    by_cases hu : Set.univ ∈ DisjointOccurrence A B
    · have ha := (disjointOccurrence_subset_inter A B hA hB hu).1
      have hb := (disjointOccurrence_subset_inter A B hA hB hu).2
      simp [law, Measure.real, hu, ha, hb]
    · simp [law, Measure.real, hu]
      positivity
  · have hp' : p < 1 := lt_of_le_of_ne p.2.2 hp
    obtain ⟨m, q, hq, hqp⟩ := exists_orParameter p hp'
    let f : E × Fin m → E := Prod.fst
    let A' := (fun ω => f '' ω) ⁻¹' A
    let B' := (fun ω => f '' ω) ⁻¹' B
    have hreal (C : Set (Set E)) (hC : MeasurableSet C) :
        (law p).real C = (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' C) := by
      have hh := law_map_image_fst (E := E) q (Fin m)
      simp only [Fintype.card_fin, hqp] at hh
      rw [← hh]
      simp only [Measure.real, Measure.map_apply (measurable_image_fst (Fin m)) hC]
      rfl
    calc
      (law p).real (DisjointOccurrence A B) =
          (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' DisjointOccurrence A B) :=
        hreal _ (measurableSet_finiteWitness _ (disjointOccurrence_upper A B)
          (finiteWitness_disjointOccurrence A B))
      _ ≤ (law q).real (DisjointOccurrence A' B') :=
        measureReal_mono (image_preimage_disjointOccurrence f A B)
      _ ≤ (law q).real A' * (law q).real B' := bk_finiteWitness_half q hq A' B'
        (fun _ _ h hω => hA (Set.image_mono h) hω)
        (fun _ _ h hω => hB (Set.image_mono h) hω)
        (finiteWitness_image_preimage f A hfA) (finiteWitness_image_preimage f B hfB)
      _ = (law p).real A * (law p).real B := by
        rw [hreal A (measurableSet_finiteWitness A hA hfA),
          hreal B (measurableSet_finiteWitness B hB hfB)]

end BK

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_Uniqueness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster events, invariant covers and uniqueness thresholds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteChanges
attribute [local instance] Classical.propDecidable


theorem exists_infinite_cluster_mono (G : BondGraph V E) {ω ω' : Set E} (h : ω ⊆ ω') :
    (∃ x, (cluster G ω x).Infinite) → ∃ x, (cluster G ω' x).Infinite := by
  rintro ⟨x, hx⟩
  exact ⟨x, hx.mono (fun _ hy => conn_mono G h hy)⟩


end FiniteChanges

section PercolationZeroOne
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] [Countable E] in
theorem infiniteClusters_nonempty_iff (G : BondGraph V E) (ω : Set E) :
    (infiniteClusters G ω).Nonempty ↔ ∃ x, (cluster G ω x).Infinite := by
  constructor
  · rintro ⟨C, hC, x, rfl⟩
    exact ⟨x, hC⟩
  · rintro ⟨x, hx⟩
    exact ⟨cluster G ω x, hx, x, rfl⟩

 theorem measurableSet_exists_infinite_cluster (G : BondGraph V E) :
    MeasurableSet {ω : Set E | ∃ x, (cluster G ω x).Infinite} := by
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion (fun x => measurableSet_infinite_cluster G x)

end PercolationZeroOne

section CoupledInterval
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

 theorem exists_infinite_cluster_probability_mono (G : BondGraph V E) {p q : unitInterval}
    (hpq : p ≤ q) :
    law p {ω | (infiniteClusters G ω).Nonempty} ≤
      law q {ω | (infiniteClusters G ω).Nonempty} := by
  have hm : MeasurableSet {ω : Set E | (infiniteClusters G ω).Nonempty} := by
    simpa only [infiniteClusters_nonempty_iff] using measurableSet_exists_infinite_cluster G
  rw [← map_openEdges p, ← map_openEdges q,
    Measure.map_apply (measurable_openEdges p) hm,
    Measure.map_apply (measurable_openEdges q) hm]
  apply measure_mono
  intro labels h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, infiniteClusters_nonempty_iff] at h ⊢
  exact exists_infinite_cluster_mono G (openEdges_mono labels hpq) h

end CoupledInterval

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Paths
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section DegreeBound
attribute [local instance] Classical.propDecidable

 theorem finite_steps (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Set.Finite {ey : E × V | G ey.1 = s(x,ey.2)} := by
  apply ((hloc x).prod (finite_neighbors hloc x)).subset
  rintro ⟨e,y⟩ he
  change G e = s(x,y) at he
  exact ⟨by change x ∈ G e; rw [he]; simp, e, he⟩

 theorem degree_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (x : V) : degree G (a x) = degree G x :=
  (Nat.card_congr (stepEquiv G h x)).symm

 theorem exists_degree_bound (G : BondGraph V E) (hqt : QuasiTransitive G) :
    ∃ D : ℕ, 0 < D ∧ ∀ x, degree G x ≤ D := by
  obtain ⟨F, hF⟩ := hqt
  refine ⟨(∑ x ∈ F, degree G x) + 1, Nat.zero_lt_succ _, ?_⟩
  intro x
  obtain ⟨o, ho, a, b, hab, rfl⟩ := hF x
  rw [degree_aut G hab]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ho).trans (Nat.le_succ _)

end DegreeBound

section SmallParameter
attribute [local instance] Classical.propDecidable

theorem trailLength_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (TrailLength G x n) := by
  rintro ω η h ⟨y,l,hl,hn,hlen,ho⟩
  exact ⟨y,l,hl,hn,hlen,fun e he => h (ho e he)⟩

theorem finiteWitness_trailLength (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (TrailLength G x n) := by
  rintro ω ⟨y,l,hl,hn,hlen,ho⟩
  exact ⟨l.toFinset, fun e he => ho e (List.mem_toFinset.mp he),
    y,l,hl,hn,hlen, fun e he => List.mem_toFinset.mpr he⟩

theorem finiteWitness_edge (e : E) : FiniteWitness {ω : Set E | e ∈ ω} := by
  intro ω he
  exact ⟨{e}, by simpa using he, by simp⟩

theorem trailLength_succ_subset (G : BondGraph V E) (x : V) (n : ℕ) :
    TrailLength G x (n+1) ⊆ ⋃ d : Step G x,
      DisjointOccurrence {ω | d.val.1 ∈ ω} (TrailLength G d.val.2 n) := by
  rintro ω ⟨y,l,hl,hn,hlen,ho⟩
  cases hl with
  | nil => simp at hlen
  | @cons x z y l e he tail =>
    refine Set.mem_iUnion.mpr ⟨⟨(e,z),he⟩, {e}, l.toFinset, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using ho e (by simp)
    · intro e' he'; exact ho e' (by simpa using Or.inr (List.mem_toFinset.mp he'))
    · simpa using (List.nodup_cons.mp hn).1
    · simp
    · exact ⟨y,l,tail,(List.nodup_cons.mp hn).2, by simpa using hlen,
        fun e' he' => List.mem_toFinset.mpr he'⟩

theorem trailLength_probability_le [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (x : V) (n : ℕ) :
    (law p).real (TrailLength G x n) ≤ ((D : ℝ) * p) ^ n := by
  induction n generalizing x with
  | zero => simpa only [pow_zero] using (measureReal_le_one (μ := law p) (s := TrailLength G x 0))
  | succ n ih =>
    let : Fintype (Step G x) := (finite_steps G hloc x).fintype
    let F := fun d : Step G x =>
      DisjointOccurrence {ω : Set E | d.val.1 ∈ ω} (TrailLength G d.val.2 n)
    calc
      (law p).real (TrailLength G x (n+1)) ≤ (law p).real (⋃ d, F d) :=
        measureReal_mono (trailLength_succ_subset G x n)
      _ ≤ ∑ d, (law p).real (F d) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _d : Step G x, (p : ℝ) * ((D : ℝ) * p) ^ n := by
        apply Finset.sum_le_sum
        intro d _
        have hb := bk p {ω : Set E | d.val.1 ∈ ω} (TrailLength G d.val.2 n)
          (fun _ _ hω he => hω he) (trailLength_upper G d.val.2 n)
          (finiteWitness_edge _) (finiteWitness_trailLength G d.val.2 n)
        have heq : (law p).real {ω : Set E | d.val.1 ∈ ω} = (p : ℝ) := by
          simpa using finite_open_probability p {d.val.1}
        rw [heq] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left (ih d.val.2) p.2.1)
      _ ≤ (D : ℝ) * ((p : ℝ) * ((D : ℝ) * p) ^ n) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg p.2.1 (pow_nonneg (mul_nonneg (Nat.cast_nonneg D) p.2.1) n))
        exact_mod_cast (show Fintype.card (Step G x) ≤ D by
          simpa only [degree, Nat.card_eq_fintype_card] using hD x)
      _ = ((D : ℝ) * p) ^ (n+1) := by ring

 theorem Along.take {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) (n : ℕ) : ∃ z, Along G x (l.take n) z := by
  induction h generalizing n with
  | @nil z => exact ⟨z, by simpa using (Along.nil (G := G) z)⟩
  | @cons x z y l e he ht ih =>
    cases n with
    | zero => exact ⟨x,.nil x⟩
    | succ n =>
      obtain ⟨v,hv⟩ := ih n
      exact ⟨v,.cons e he hv⟩

 theorem infinite_cluster_subset_trailLength (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (n : ℕ) : {ω | (cluster G ω x).Infinite} ⊆ TrailLength G x n := by
  intro ω hω
  obtain ⟨y,hy,hyball⟩ := hω.exists_notMem_finite (finite_reachBall hloc x n)
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G hy
  have hlen : n ≤ l.length := by
    by_contra h
    exact hyball ((reachBall_mono G x (le_of_lt (Nat.lt_of_not_ge h))) hl.mem_reachBall)
  obtain ⟨z,hz⟩ := hl.take n
  exact ⟨z,l.take n,hz,hn.take,List.length_take_of_le hlen,
    fun e he => ho e (List.mem_of_mem_take he)⟩

 theorem infinite_cluster_probability_eq_zero_of_small [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp : (D : ℝ) * p < 1) (x : V) :
    law p {ω | (cluster G ω x).Infinite} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg (Nat.cast_nonneg D) p.2.1) hp)
  filter_upwards [] with n
  exact (measureReal_mono (infinite_cluster_subset_trailLength G hloc x n)).trans
    (trailLength_probability_le G hloc D hD p x n)

 theorem exists_infinite_cluster_probability_eq_zero_of_small [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp : (D : ℝ) * p < 1) :
    law p {ω | (infiniteClusters G ω).Nonempty} = 0 := by
  have heq : {ω | (infiniteClusters G ω).Nonempty} =
      ⋃ x : V, {ω | (cluster G ω x).Infinite} := by
    ext ω
    simp only [Set.mem_ofPred_eq, infiniteClusters_nonempty_iff, Set.mem_iUnion]
  rw [heq, measure_iUnion_null_iff]
  exact infinite_cluster_probability_eq_zero_of_small G hloc D hD p hp

 theorem pc_pos [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) :
    0 < pc G := by
  obtain ⟨D, hDpos, hD⟩ := exists_degree_bound G hqt
  let t : unitInterval := ⟨1 / ((D : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) D]⟩
  have ht : (0 : unitInterval) < t := by
    change (0 : ℝ) < 1 / ((D : ℝ) + 1)
    positivity
  apply ht.trans_le
  apply le_sInf
  intro p hp
  by_contra h
  have hp' : (p : ℝ) < 1 / ((D : ℝ) + 1) := lt_of_not_ge h
  have hsmall : (D : ℝ) * p < 1 := by
    have hmul := (lt_div_iff₀ (show (0 : ℝ) < D + 1 by positivity)).mp hp'
    nlinarith [p.2.1]
  have hz := exists_infinite_cluster_probability_eq_zero_of_small G hloc D hD p hsmall
  exact (ne_of_gt hp) hz

end SmallParameter

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Sprinkling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

section SprinklingPaths
attribute [local instance] Classical.propDecidable

 
theorem Along.first_outside {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) (S : Set E) :
    (∀ e ∈ l, e ∈ S) ∨ ∃ a b e l₁ l₂,
      l = l₁ ++ e :: l₂ ∧ Along G x l₁ a ∧ G e = s(a,b) ∧
      Along G b l₂ y ∧ (∀ d ∈ l₁, d ∈ S) ∧ e ∉ S := by
  induction h with
  | nil => left; simp
  | @cons x z y l e he ht ih =>
    by_cases hes : e ∈ S
    · rcases ih with hall | ⟨a,b,d,l₁,l₂,hl,h₁,hd,h₂,hopen,hnot⟩
      · left
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hes hall
      · right
        refine ⟨a,b,d,e::l₁,l₂,by simp [hl], .cons e he h₁, hd, h₂, ?_, hnot⟩
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hes hopen
    · right
      exact ⟨x,z,e,[],l,rfl,.nil x,he,ht,by simp,hes⟩


end SprinklingPaths

section ColoredSprinkling
attribute [local instance] Classical.propDecidable

 theorem finiteWitness_inter (A : Set (Set E)) (hA : FiniteWitness A) (S : Set E) :
    FiniteWitness {ω | ω ∩ S ∈ A} := by
  intro ω h
  obtain ⟨s,hs,hsa⟩ := hA (ω ∩ S) h
  refine ⟨s,hs.trans Set.inter_subset_left,?_⟩
  have he : (s : Set E) ∩ S = s := Set.inter_eq_left.mpr (hs.trans Set.inter_subset_right)
  change (s : Set E) ∩ S ∈ A
  rwa [he]

end ColoredSprinkling

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Sharpness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteRusso
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem bernoulliPolynomial_congr (s : Finset E) {f g : Finset E → ℝ}
    (h : ∀ t ⊆ s, f t = g t) (p : ℝ) :
    bernoulliPolynomial s f p = bernoulliPolynomial s g p := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_powerset.mp ht)]

theorem bernoulliPolynomial_sub (s : Finset E) (f g : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => f t-g t) p =
      bernoulliPolynomial s f p - bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial, sub_mul, Finset.sum_sub_distrib]


theorem hasDerivAt_bernoulliPolynomial (s : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    HasDerivAt (bernoulliPolynomial s f)
      (∑ e ∈ s, bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p) p := by
  induction s using Finset.induction_on generalizing f with
  | empty =>
    convert hasDerivAt_const p (f ∅) using 1 <;> try rfl
    · funext q
      exact bernoulliPolynomial_empty f q
  | @insert e s he ih =>
    have hd := (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul (ih f)).add
      ((hasDerivAt_id p).mul (ih (fun t => f (insert e t))))
    have hf : bernoulliPolynomial (insert e s) f =
        fun q => (1-q)*bernoulliPolynomial s f q +
          q*bernoulliPolynomial s (fun t => f (insert e t)) q :=
      funext fun q => bernoulliPolynomial_insert s e he f q
    rw [hf]
    convert hd using 1 <;> try rfl
    have hs : ∑ a ∈ s, bernoulliPolynomial ((insert e s).erase a)
          (fun t => f (insert a t)-f t) p =
        (1-p)*(∑ a ∈ s, bernoulliPolynomial (s.erase a) (fun t => f (insert a t)-f t) p) +
        p*(∑ a ∈ s, bernoulliPolynomial (s.erase a)
          (fun t => f (insert e (insert a t))-f (insert e t)) p) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have hae : e ≠ a := (ne_of_mem_of_not_mem ha he).symm
      rw [Finset.erase_insert_of_ne hae, bernoulliPolynomial_insert _ e
        (fun hh => he (Finset.mem_of_mem_erase hh))]
      congr 2
      apply bernoulliPolynomial_congr
      intro t _
      rw [Finset.insert_comm e a]
    simp only [Finset.sum_insert he, Finset.erase_insert he, zero_sub, neg_one_mul,
      one_mul, Pi.sub_apply, id_eq]
    rw [hs, bernoulliPolynomial_sub]
    ring

theorem bernoulliPolynomial_nonneg (s : Finset E) (f : Finset E → ℝ) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hf : ∀ t ⊆ s, 0 ≤ f t) :
    0 ≤ bernoulliPolynomial s f p := by
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (mul_nonneg (hf t (Finset.mem_powerset.mp ht))
    (pow_nonneg hp.1 _)) (pow_nonneg (sub_nonneg.mpr hp.2) _)

theorem bernoulliPolynomial_mono (s : Finset E) (f g : Finset E → ℝ) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hfg : ∀ t ⊆ s, f t ≤ g t) :
    bernoulliPolynomial s f p ≤ bernoulliPolynomial s g p := by
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hfg t (Finset.mem_powerset.mp ht)) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

 
theorem bernoulliPolynomial_union (s t : Finset E) (hdis : Disjoint s t)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t) f p =
      bernoulliPolynomial s (fun a => bernoulliPolynomial t (fun b => f (a ∪ b)) p) p := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert e s he ih =>
    have hed : e ∉ t := (Finset.disjoint_insert_left.mp hdis).1
    have hst : Disjoint s t := (Finset.disjoint_insert_left.mp hdis).2
    rw [Finset.insert_union, bernoulliPolynomial_insert _ e (by simp [he, hed]),
      bernoulliPolynomial_insert s e he, ih hst, ih hst]
    congr 2
    apply bernoulliPolynomial_congr
    intro a _
    apply bernoulliPolynomial_congr
    intro b _
    rw [Finset.insert_union]

 

theorem bernoulliPolynomial_closed_difference (s : Finset E) (e : E) (he : e ∈ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => if e ∈ t then 0 else f (insert e t)-f t) p =
      (1-p)*bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
  have hes : e ∉ s.erase e := Finset.notMem_erase e s
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e hes]
  have hc : bernoulliPolynomial (s.erase e)
      (fun t => if e ∈ t then 0 else f (insert e t)-f t) p =
      bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
    apply bernoulliPolynomial_congr
    intro t ht
    simp [show e ∉ t from fun h => hes (ht h)]
  rw [hc]
  simp

theorem closed_difference_russo (s : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    (1-p)*deriv (bernoulliPolynomial s f) p =
      ∑ e ∈ s, bernoulliPolynomial s
        (fun t => if e ∈ t then 0 else f (insert e t)-f t) p := by
  rw [(hasDerivAt_bernoulliPolynomial s f p).deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact (bernoulliPolynomial_closed_difference s e he f p).symm


theorem finiteEventPolynomial_eq (s : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial s A (p : ℝ) = finiteProbability p s A := by
  unfold finiteEventPolynomial bernoulliPolynomial finiteProbability
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : (t : Set E) ∈ A <;> simp [ht]


theorem closedPivotal_difference (A : Set (Set E)) (hA : IsUpperSet A) (e : E)
    (t : Finset E) :
    (if (t : Set E) ∈ closedPivotal A e then (1:ℝ) else 0) =
    (if e ∈ t then 0 else
      (if ((insert e t : Finset E) : Set E) ∈ A then (1:ℝ) else 0) -
      (if (t : Set E) ∈ A then 1 else 0)) := by
  by_cases he : e ∈ t
  · simp [closedPivotal, he]
  · by_cases ha : (t : Set E) ∈ A
    · have hi : insert e (t : Set E) ∈ A := hA (Set.subset_insert e _) ha
      simp [closedPivotal, he, ha, hi]
    · by_cases hi : insert e (t : Set E) ∈ A <;> simp [closedPivotal, he, ha, hi]


end FiniteRusso

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem mem_unexposed_of_conn (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∈ unexposed G Λ ω) (hxy : Conn G ω x y) :
    y ∈ unexposed G Λ ω := by
  intro z hyz
  exact hx z (hxy.trans hyz)

 
theorem conn_restrict_unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∈ unexposed G Λ ω) (hxy : Conn G ω x y) :
    Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x y := by
  induction hxy with
  | refl => exact conn_refl _ _ _
  | @tail y z hxy hyz ih =>
    obtain ⟨e,he,hends⟩ := hyz
    have hy : y ∈ unexposed G Λ ω := mem_unexposed_of_conn G Λ ω hx hxy
    have hz : z ∈ unexposed G Λ ω := mem_unexposed_of_conn G Λ ω hy (.single ⟨e,he,hends⟩)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e y z hends).mpr ⟨hy,hz⟩⟩,hends⟩

 
theorem unexposed_boundary_closed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {e : E} {a b : V} (he : G e = s(a,b))
    (ha : a ∈ unexposed G Λ ω) (hb : b ∉ unexposed G Λ ω) : e ∉ ω := by
  intro ho
  exact hb (mem_unexposed_of_conn G Λ ω ha (.single ⟨e,ho,he⟩))

 

theorem unexposed_insert_crossing (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {e : E} {a b x : V} (he : G e = s(a,b))
    (hx : x ∈ unexposed G Λ ω) (_ha : a ∈ unexposed G Λ ω)
    (hb : b ∉ unexposed G Λ ω) :
    x ∉ unexposed G Λ (insert e ω) ↔
      Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x a := by
  classical
  constructor
  · intro hn
    obtain ⟨y,hxy,hy⟩ := by simpa [unexposed, not_forall, Classical.not_imp] using hn
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | h | h
    · exact (hy (hx y h)).elim
    · exact conn_restrict_unexposed G Λ ω hx h.1
    · exact (hb (mem_unexposed_of_conn G Λ ω hx h.1)).elim
  · intro hxa hn
    have hxa' : Conn G ω x a := conn_mono G Set.inter_subset_left hxa
    apply hb
    intro y hby
    exact hn y ((conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨hxa',hby⟩)))

 
theorem not_mem_unexposed_of_conn (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ unexposed G Λ ω) (hxy : Conn G ω x y) :
    y ∉ unexposed G Λ ω := by
  intro hy
  exact hx (mem_unexposed_of_conn G Λ ω hy (conn_symm G ω hxy))

 
theorem conn_sdiff_internal_unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ unexposed G Λ ω) (hxy : Conn G ω x y) :
    Conn G (ω \ internalEdges G (unexposed G Λ ω)) x y := by
  induction hxy with
  | refl => exact conn_refl _ _ _
  | @tail y z hxy hyz ih =>
    obtain ⟨e,he,hends⟩ := hyz
    have hy : y ∉ unexposed G Λ ω := not_mem_unexposed_of_conn G Λ ω hx hxy
    exact ih.tail ⟨e,⟨he,fun hi => hy ((mem_internalEdges_of_ends G _ e y z hends).mp hi).1⟩,hends⟩

 
theorem unexposed_sdiff_internal (G : BondGraph V E) (Λ : Set V) (ω : Set E) :
    unexposed G Λ (ω \ internalEdges G (unexposed G Λ ω)) = unexposed G Λ ω := by
  ext x
  constructor
  · intro hx
    by_contra hn
    apply hn
    intro y hxy
    exact hx y (conn_sdiff_internal_unexposed G Λ ω hn hxy)
  · intro hx y hxy
    exact hx y (conn_mono G Set.sdiff_subset hxy)

 
theorem unexposed_union_internal (G : BondGraph V E) (Λ : Set V) (ω η : Set E)
    (hη : η ⊆ internalEdges G (unexposed G Λ ω)) :
    unexposed G Λ (ω ∪ η) = unexposed G Λ ω := by
  ext x
  constructor
  · intro hx y hxy
    exact hx y (conn_mono G Set.subset_union_left hxy)
  · intro hx y hxy
    suffices hy : y ∈ unexposed G Λ ω from unexposed_subset G Λ ω hy
    induction hxy with
    | refl => exact hx
    | @tail y z hxy hyz ih =>
      obtain ⟨e,hωe,he⟩ := hyz
      rcases hωe with ho | hηe
      · exact mem_unexposed_of_conn G Λ ω ih (.single ⟨e,ho,he⟩)
      · exact ((mem_internalEdges_of_ends G _ e y z he).mp (hη hηe)).2

 
theorem unexposed_union_eq_iff (G : BondGraph V E) (Λ S : Set V) (a b : Set E)
    (ha : a ⊆ internalEdges G S) (hb : Disjoint b (internalEdges G S)) :
    unexposed G Λ (a ∪ b) = S ↔ unexposed G Λ b = S := by
  constructor
  · intro h
    have he : (a ∪ b) \ internalEdges G S = b := by
      ext e
      constructor
      · rintro ⟨he,hn⟩
        exact he.resolve_left (fun he => hn (ha he))
      · intro he
        exact ⟨Or.inr he,fun hi => Set.disjoint_left.mp hb he hi⟩
    simpa only [h, he] using unexposed_sdiff_internal G Λ (a ∪ b)
  · intro h
    have he := unexposed_union_internal G Λ b a (h ▸ ha)
    simpa only [Set.union_comm b a,h] using he


theorem escapeEvent_isUpperSet (G : BondGraph V E) (Λ : Set V) (x : V) :
    IsUpperSet (escapeEvent G Λ x) := by
  intro ω η hωη hx hη
  apply hx
  intro y hxy
  exact hη y (conn_mono G hωη hxy)

 
theorem escape_closed_pivotal_iff (G : BondGraph V E) (Λ : Set V)
    (ω : Set E) (x : V) (e : E) :
    (e ∉ ω ∧ ω ∉ escapeEvent G Λ x ∧ insert e ω ∈ escapeEvent G Λ x) ↔
      x ∈ unexposed G Λ ω ∧ ∃ a b,
        G e = s(a,b) ∧ a ∈ unexposed G Λ ω ∧ b ∉ unexposed G Λ ω ∧
        Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x a := by
  classical
  constructor
  · rintro ⟨_,hx,hn⟩
    have hx' : x ∈ unexposed G Λ ω := by simpa [escapeEvent] using hx
    refine ⟨hx',?_⟩
    obtain ⟨⟨a,b⟩,he'⟩ := Sym2.mk_surjective (G e)
    have he : G e = s(a,b) := he'.symm
    obtain ⟨y,hxy,hy⟩ := by simpa [escapeEvent,unexposed,not_forall,Classical.not_imp] using hn
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | h | h
    · exact (hy (hx' y h)).elim
    · exact ⟨a,b,he,mem_unexposed_of_conn G Λ ω hx' h.1,
        fun hb => hy (hb y h.2),conn_restrict_unexposed G Λ ω hx' h.1⟩
    · exact ⟨b,a,he.trans (Sym2.eq_swap ..),mem_unexposed_of_conn G Λ ω hx' h.1,
        fun ha => hy (ha y h.2),conn_restrict_unexposed G Λ ω hx' h.1⟩
  · rintro ⟨hx,a,b,he,ha,hb,hxa⟩
    exact ⟨unexposed_boundary_closed G Λ ω he ha hb,by simpa [escapeEvent] using hx,
      (unexposed_insert_crossing G Λ ω he hx ha hb).mpr hxa⟩

attribute [local instance] Classical.decEq

 theorem bernoulliPolynomial_add (s : Finset E) (f g : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => f t+g t) p =
      bernoulliPolynomial s f p + bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial, add_mul, Finset.sum_add_distrib]

 theorem bernoulliPolynomial_mul_const (s : Finset E) (f : Finset E → ℝ) (c p : ℝ) :
    bernoulliPolynomial s (fun t => f t*c) p = bernoulliPolynomial s f p*c := by
  simp only [bernoulliPolynomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  ring

 theorem bernoulliPolynomial_const_mul (s : Finset E) (f : Finset E → ℝ) (c p : ℝ) :
    bernoulliPolynomial s (fun t => c*f t) p = c*bernoulliPolynomial s f p := by
  simpa only [mul_comm c] using bernoulliPolynomial_mul_const s f c p

 theorem bernoulliPolynomial_sum {ι : Type*} (s : Finset E) (I : Finset ι)
    (f : ι → Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => ∑ i ∈ I, f i t) p =
      ∑ i ∈ I, bernoulliPolynomial s (f i) p := by
  classical
  simp only [bernoulliPolynomial, Finset.sum_mul]
  exact Finset.sum_comm



theorem bernoulliPolynomial_exposure (G : BondGraph V E) (Λ S : Set V)
    (s t : Finset E) (hs : (s : Set E) ⊆ internalEdges G S)
    (ht : Disjoint (t : Set E) (internalEdges G S)) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t)
      (fun a => (if unexposed G Λ (a : Set E) = S then (1:ℝ) else 0) * f (a ∩ s)) p =
    bernoulliPolynomial t (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p *
      bernoulliPolynomial s f p := by
  have hdis : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp ht hf (hs he)
  rw [bernoulliPolynomial_union s t hdis]
  trans bernoulliPolynomial s (fun a =>
    bernoulliPolynomial t (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p * f a) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [← bernoulliPolynomial_mul_const]
    apply bernoulliPolynomial_congr
    intro b hb
    have hab : unexposed G Λ ((a ∪ b : Finset E) : Set E) = S ↔
        unexposed G Λ (b : Set E) = S := by
      rw [Finset.coe_union]
      exact unexposed_union_eq_iff G Λ S _ _ (fun _ he => hs (ha he))
        (ht.mono_left (by exact_mod_cast hb))
    have hbs : b ∩ s = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp (hdis.symm.mono_left hb)
    rw [Finset.union_inter_distrib_right,Finset.inter_eq_left.mpr ha,hbs,Finset.union_empty]
    simp only [hab]
  · exact bernoulliPolynomial_const_mul s f _ p


theorem unexposedRegion_subset (G : BondGraph V E) (Λ : Finset V) (ω : Set E) :
    unexposedRegion G Λ ω ⊆ Λ := by
  intro x hx
  apply unexposed_subset G (Λ : Set V) ω
  simpa only [← coe_unexposedRegion,Finset.mem_coe] using hx

 
theorem bernoulliPolynomial_partition_region (G : BondGraph V E) (Λ : Finset V)
    (F : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial F f p = ∑ S ∈ Λ.powerset,
      bernoulliPolynomial F
        (fun t => if unexposed G (Λ : Set V) (t : Set E) = (S : Set V) then f t else 0) p := by
  rw [← bernoulliPolynomial_sum]
  apply bernoulliPolynomial_congr
  intro t _
  symm
  rw [Finset.sum_eq_single (unexposedRegion G Λ (t : Set E))]
  · simp
  · intro S _ hne
    have hh : unexposed G (Λ : Set V) (t : Set E) ≠ (S : Set V) := by
      intro he
      apply hne
      apply Finset.coe_injective
      exact he.symm.trans (coe_unexposedRegion G Λ (t : Set E)).symm
    simp [hh]
  · intro hn
    exact (hn (Finset.mem_powerset.mpr (unexposedRegion_subset G Λ (t : Set E)))).elim


 theorem internalSupport_subset (G : BondGraph V E) (S : Set V) (F : Finset E) :
    internalSupport G S F ⊆ F := Finset.filter_subset _ _

 theorem internalSupport_union_sdiff (G : BondGraph V E) (S : Set V) (F : Finset E) :
    internalSupport G S F ∪ (F \ internalSupport G S F) = F :=
  Finset.union_sdiff_of_subset (internalSupport_subset G S F)

 theorem coe_inter_internalSupport (G : BondGraph V E) (S : Set V) (F t : Finset E)
    (ht : t ⊆ F) : ((t ∩ internalSupport G S F : Finset E) : Set E) =
      (t : Set E) ∩ internalEdges G S := by
  ext e
  simp only [Finset.mem_coe,Finset.mem_inter,internalSupport,Finset.mem_filter,Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,ht h.1,h.2⟩⟩


 theorem regionProbability_nonneg (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ regionProbability G Λ S F p := by
  apply bernoulliPolynomial_nonneg _ _ _ hp
  intro t _
  split_ifs <;> norm_num

 
theorem bernoulliPolynomial_exposure_factor (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial F
      (fun t => (if unexposed G Λ (t : Set E) = S then (1:ℝ) else 0) *
        f (t ∩ internalSupport G S F)) p =
      regionProbability G Λ S F p * bernoulliPolynomial (internalSupport G S F) f p := by
  let s := internalSupport G S F
  let t := F \ s
  have hs : (s : Set E) ⊆ internalEdges G S := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have ht : Disjoint (t : Set E) (internalEdges G S) := by
    apply Set.disjoint_left.mpr
    intro e he hi
    have he' := Finset.mem_sdiff.mp he
    exact he'.2 (Finset.mem_filter.mpr ⟨he'.1,hi⟩)
  have he : s ∪ t = F := internalSupport_union_sdiff G S F
  have hq : bernoulliPolynomial t
      (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p =
      regionProbability G Λ S F p := by
    simpa only [he,mul_one,bernoulliPolynomial_const,regionProbability] using
      (bernoulliPolynomial_exposure G Λ S s t hs ht (fun _ => 1) p).symm
  simpa only [he,hq] using bernoulliPolynomial_exposure G Λ S s t hs ht f p


theorem finite_escape_russo (G : BondGraph V E) (Λ : Set V) (x : V)
    (F : Finset E) (p : ℝ) :
    (1-p)*deriv (finiteEventPolynomial F (escapeEvent G Λ x)) p =
      bernoulliPolynomial F (fun t => closedEscapeCount G Λ x F (t : Set E)) p := by
  unfold finiteEventPolynomial
  rw [closed_difference_russo]
  unfold closedEscapeCount
  rw [bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply bernoulliPolynomial_congr
  intro t _
  exact (closedPivotal_difference _ (escapeEvent_isUpperSet G Λ x) e t).symm

 
theorem closedEscapeCount_expectation (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) :
    bernoulliPolynomial F (fun t => closedEscapeCount G Λ x F (t : Set E)) p =
      ∑ S ∈ Λ.powerset, if x ∈ S then
        regionProbability G Λ S F p * boundaryExpectation G S x F p else 0 := by
  rw [bernoulliPolynomial_partition_region G Λ F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    unfold boundaryExpectation
    rw [← bernoulliPolynomial_exposure_factor G Λ S F
      (fun t => crossingCount G S x F (t : Set E)) p]
    apply bernoulliPolynomial_congr
    intro t ht
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V)
    · simp only [hreg,if_true,one_mul]
      apply Finset.sum_congr rfl
      intro e _
      have hc : (t : Set E) ∈ closedPivotal (escapeEvent G Λ x) e ↔
          crossingReach G S x ((t ∩ internalSupport G S F : Finset E) : Set E) e := by
        simpa only [closedPivotal,Set.mem_ofPred_eq,hreg,Finset.mem_coe,hx,true_and,
          coe_inter_internalSupport G S F t ht,crossingReach] using
          escape_closed_pivotal_iff G Λ (t : Set E) x e
      exact if_congr hc rfl rfl
    · simp [hreg]
  · rw [ite_eq_right hx,← bernoulliPolynomial_zero F p]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V)
    · simp only [hreg,if_true]
      apply Finset.sum_eq_zero
      intro e _
      have hn : (t : Set E) ∉ closedPivotal (escapeEvent G Λ x) e := by
        intro he
        have hh := ((escape_closed_pivotal_iff G Λ (t : Set E) x e).mp he).1
        apply hx
        simpa only [hreg,Finset.mem_coe] using hh
      simp [hn]
    · simp [hreg]

 
theorem finite_escape_complement (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) :
    1-finiteEventPolynomial F (escapeEvent G Λ x) p =
      ∑ S ∈ Λ.powerset, if x ∈ S then regionProbability G Λ S F p else 0 := by
  have he : 1-finiteEventPolynomial F (escapeEvent G Λ x) p =
      bernoulliPolynomial F
        (fun t => if x ∈ unexposed G (Λ : Set V) (t : Set E) then (1:ℝ) else 0) p := by
    change 1-bernoulliPolynomial F (fun t => if (t : Set E) ∈ escapeEvent G Λ x then 1 else 0) p = _
    rw [show (1:ℝ) = bernoulliPolynomial F (fun _ => 1) p from (bernoulliPolynomial_const F 1 p).symm]
    rw [← bernoulliPolynomial_sub]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hx : x ∈ unexposed G (Λ : Set V) (t : Set E) <;> simp [escapeEvent,hx,bernoulliPolynomial_const]
  rw [he,bernoulliPolynomial_partition_region G Λ F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V) <;> simp [hreg,hx]
  · rw [ite_eq_right hx,← bernoulliPolynomial_zero F p]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V) <;> simp [hreg,hx]

 

theorem finite_escape_differential_lower (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hcost : ∀ S ⊆ Λ, x ∈ S → 1 ≤ p*boundaryExpectation G (S : Set V) x F p) :
    1-finiteEventPolynomial F (escapeEvent G Λ x) p ≤
      p*(1-p)*deriv (finiteEventPolynomial F (escapeEvent G Λ x)) p := by
  rw [mul_assoc,finite_escape_russo,closedEscapeCount_expectation,finite_escape_complement,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  by_cases hx : x ∈ S
  · simp only [ite_eq_left hx]
    have hq := regionProbability_nonneg G Λ S F p hp
    calc
      regionProbability G Λ S F p ≤
          regionProbability G Λ S F p * (p*boundaryExpectation G S x F p) :=
        le_mul_of_one_le_right hq (hcost S (Finset.mem_powerset.mp hS) hx)
      _ = p*(regionProbability G Λ S F p * boundaryExpectation G S x F p) := by ring
  · simp [hx]

 theorem bernoulliPolynomial_monotoneOn (F : Finset E) (f : Finset E → ℝ)
    (hf : ∀ a b, a ⊆ b → f a ≤ f b) :
    MonotoneOn (bernoulliPolynomial F f) (Set.Icc (0:ℝ) 1) := by
  have hd : Differentiable ℝ (bernoulliPolynomial F f) :=
    fun q => (hasDerivAt_bernoulliPolynomial F f q).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hd.continuous.continuousOn hd.differentiableOn
  intro q hq
  have hq' : q ∈ Set.Icc (0:ℝ) 1 := interior_subset hq
  rw [(hasDerivAt_bernoulliPolynomial F f q).deriv]
  apply Finset.sum_nonneg
  intro e _
  apply bernoulliPolynomial_nonneg _ _ _ hq'
  intro t _
  exact sub_nonneg.mpr (hf t (insert e t) (Finset.subset_insert e t))

 theorem crossingCount_mono (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) {ω η : Set E} (h : ω ⊆ η) :
    crossingCount G S x F ω ≤ crossingCount G S x F η := by
  apply Finset.sum_le_sum
  intro e _
  have hh : crossingReach G S x ω e → crossingReach G S x η e := by
    rintro ⟨a,b,he,ha,hb,hc⟩
    exact ⟨a,b,he,ha,hb,conn_mono G h hc⟩
  by_cases hω : crossingReach G S x ω e
  · simp [hω,hh hω]
  · simp only [ite_eq_right hω]
    split_ifs <;> norm_num

 theorem boundaryExpectation_nonneg (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ boundaryExpectation G S x F p := by
  apply bernoulliPolynomial_nonneg _ _ _ hp
  intro t _
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

 theorem boundaryExpectation_monotoneOn (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) : MonotoneOn (boundaryExpectation G S x F) (Set.Icc (0:ℝ) 1) := by
  apply bernoulliPolynomial_monotoneOn
  intro a b hab
  exact crossingCount_mono G S x F (by exact_mod_cast hab)

 theorem boundaryCost_monotoneOn (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) : MonotoneOn (fun p => p*boundaryExpectation G S x F p)
      (Set.Icc (0:ℝ) 1) := by
  intro p hp q hq hpq
  exact mul_le_mul hpq (boundaryExpectation_monotoneOn G S x F hp hq hpq)
    (boundaryExpectation_nonneg G S x F p hp) hq.1

 theorem finiteEventPolynomial_mem_Icc (F : Finset E) (A : Set (Set E))
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    finiteEventPolynomial F A p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply bernoulliPolynomial_nonneg _ _ _ hp
    intro t _
    split_ifs <;> norm_num
  · calc
      finiteEventPolynomial F A p ≤ bernoulliPolynomial F (fun _ => 1) p := by
        apply bernoulliPolynomial_mono _ _ _ _ hp
        intro t _
        split_ifs <;> norm_num
      _ = 1 := bernoulliPolynomial_const F 1 p

 

theorem differential_escape_growth {f : ℝ → ℝ} {r p : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (hp : p < 1)
    (hf : Differentiable ℝ f) (hbound : ∀ q ∈ Set.Icc r p, f q ∈ Set.Icc (0:ℝ) 1)
    (hineq : ∀ q ∈ Set.Icc r p, 1-f q ≤ q*(1-q)*deriv f q) :
    1-Real.exp (r-p) ≤ f p := by
  have hd (q : ℝ) : HasDerivAt (fun u => Real.exp u*(1-f u))
      (Real.exp q*(1-f q)+Real.exp q*(0-deriv f q)) q :=
    (Real.hasDerivAt_exp q).mul ((hasDerivAt_const q 1).sub (hf q).hasDerivAt)
  have hanti : AntitoneOn (fun q => Real.exp q*(1-f q)) (Set.Icc r p) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc r p)
      (Real.continuous_exp.mul (continuous_const.sub hf.continuous)).continuousOn
      (fun q _ => (hd q).hasDerivWithinAt)
    intro q hq
    have hqi : q ∈ Set.Icc r p := interior_subset hq
    have hq0 : 0 < q := hr.trans_le hqi.1
    have hq1 : q < 1 := hqi.2.trans_lt hp
    have hcoef : 0 < q*(1-q) := mul_pos hq0 (sub_pos.mpr hq1)
    have hder : 0 ≤ deriv f q := nonneg_of_mul_nonneg_right
      ((sub_nonneg.mpr (hbound q hqi).2).trans (hineq q hqi)) hcoef
    have hc : q*(1-q) ≤ 1 := by nlinarith [sq_nonneg q]
    have hsmall : 1-f q ≤ deriv f q := (hineq q hqi).trans
      (mul_le_of_le_one_left hder hc)
    have hn := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos q).le
      (show 1-f q-deriv f q ≤ 0 by linarith)
    nlinarith only [hn]
  have hle := hanti (show r ∈ Set.Icc r p from ⟨le_rfl,hrp⟩)
    (show p ∈ Set.Icc r p from ⟨hrp,le_rfl⟩) hrp
  have he : Real.exp p*(1-f p) ≤ Real.exp r := by
    calc
      Real.exp p*(1-f p) ≤ Real.exp r*(1-f r) := hle
      _ ≤ Real.exp r := mul_le_of_le_one_right (Real.exp_pos r).le
        (by linarith [(hbound r ⟨le_rfl,hrp⟩).1])
  have hfin : 1-f p ≤ Real.exp (r-p) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos p)).mpr
    simpa only [mul_comm] using he
  linarith

 

theorem finite_escape_probability_lower (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (r p : ℝ) (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S ⊆ Λ, x ∈ S → 1 ≤ r*boundaryExpectation G (S : Set V) x F r) :
    0 < 1-Real.exp (r-p) ∧
      1-Real.exp (r-p) ≤ finiteEventPolynomial F (escapeEvent G Λ x) p := by
  have hrI : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr.le,(hrp.trans hp).le⟩
  have hqI (q : ℝ) (hq : q ∈ Set.Icc r p) : q ∈ Set.Icc (0:ℝ) 1 :=
    ⟨hr.le.trans hq.1,hq.2.trans hp.le⟩
  refine ⟨sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hrp)),?_⟩
  apply differential_escape_growth hr hrp.le hp
  · intro q
    exact (hasDerivAt_bernoulliPolynomial F _ q).differentiableAt
  · intro q hq
    exact finiteEventPolynomial_mem_Icc F _ q (hqI q hq)
  · intro q hq
    apply finite_escape_differential_lower G Λ x F q (hqI q hq)
    intro S hS hx
    exact (hcost S hS hx).trans (boundaryCost_monotoneOn G S x F hrI (hqI q hq) hq.1)

end ExteriorExposure

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology

theorem bernoulliPolynomial_map {F : Type*} (f : E ↪ F) (s : Finset E)
    (h : Finset F → ℝ) (p : ℝ) :
    bernoulliPolynomial (s.map f) h p =
      bernoulliPolynomial s (fun t => h (t.map f)) p := by
  induction s using Finset.induction_on generalizing h with
  | empty => simp
  | @insert e s he ih =>
    rw [Finset.map_insert,bernoulliPolynomial_insert _ (f e) (by simpa using he),
      bernoulliPolynomial_insert s e he,ih,ih]
    simp only [Finset.map_insert]

theorem finiteEventPolynomial_restrict (F : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial F A (p : ℝ) = (law p).real {ω | ω ∩ (F : Set E) ∈ A} := by
  let f : (F : Set E) ↪ E := ⟨Subtype.val,Subtype.val_injective⟩
  have hm : (Finset.univ : Finset (F : Set E)).map f = F := by
    ext e
    simp [f]
  have he : finiteEventPolynomial F A (p : ℝ) =
      finiteEventPolynomial (Finset.univ : Finset (F : Set E))
        {η | f '' η ∈ A} (p : ℝ) := by
    unfold finiteEventPolynomial
    calc
      bernoulliPolynomial F (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ) =
        bernoulliPolynomial (Finset.univ.map f) (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ) :=
          congrArg (fun H => bernoulliPolynomial H (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ)) hm.symm
      _ = _ := by
        rw [bernoulliPolynomial_map]
        apply bernoulliPolynomial_congr
        intro t _
        simp only [Finset.coe_map]
        rfl
  rw [he,finiteEventPolynomial_eq,finiteProbability_univ,← law_map_restrict p (F : Set E),
    measureReal_def,Measure.map_apply (measurable_set_restrict _) .of_discrete]
  congr 2
  ext ω
  have hh : f '' (Subtype.val ⁻¹' ω : Set (F : Set E)) = ω ∩ (F : Set E) := by
    ext e
    simp [f,and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,hh]

theorem bernoulliPolynomial_restrict (F H : Finset E) (hFH : F ⊆ H)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial H (fun t => f (t ∩ F)) p = bernoulliPolynomial F f p := by
  rw [← Finset.union_sdiff_of_subset hFH,bernoulliPolynomial_union _ _ Finset.disjoint_sdiff]
  trans bernoulliPolynomial F (fun a => f a) p
  · apply bernoulliPolynomial_congr
    intro a ha
    trans bernoulliPolynomial (H \ F) (fun _ => f a) p
    · apply bernoulliPolynomial_congr
      intro b hb
      have hdis : Disjoint b F := (Finset.disjoint_sdiff.symm).mono_left hb
      rw [Finset.union_inter_distrib_right,Finset.inter_eq_left.mpr ha,
        Finset.disjoint_iff_inter_eq_empty.mp hdis,Finset.union_empty]
    · exact bernoulliPolynomial_const _ _ _
  · rfl


theorem escapeEvent_restrict_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) (ω : Set E) :
    ω ∩ (incidentSupport G hloc Λ : Set E) ∈ escapeEvent G Λ x ↔
      ω ∈ escapeEvent G Λ x := by
  constructor
  · exact escapeEvent_isUpperSet G Λ x Set.inter_subset_left
  · intro hx
    by_contra hn
    have hx' : x ∈ unexposed G Λ (ω ∩ (incidentSupport G hloc Λ : Set E)) := by
      simpa only [escapeEvent,Set.mem_ofPred_eq,not_not] using hn
    apply hx
    intro y hxy
    have hc : Conn G (ω ∩ (incidentSupport G hloc Λ : Set E)) x y := by
      induction hxy with
      | refl => exact conn_refl _ _ _
      | @tail a b hxa hab ih =>
        obtain ⟨e,he,heab⟩ := hab
        have ha : a ∈ Λ := hx' a ih
        have hF : e ∈ incidentSupport G hloc Λ :=
          (mem_incidentSupport G hloc Λ e).mpr ⟨a,ha,by simp [heab]⟩
        exact ih.tail ⟨e,⟨he,hF⟩,heab⟩
    exact hx' y hc

theorem finite_escape_eq_law (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) (p : unitInterval) :
    finiteEventPolynomial (incidentSupport G hloc Λ) (escapeEvent G Λ x) (p : ℝ) =
      (law p).real (escapeEvent G Λ x) := by
  rw [finiteEventPolynomial_restrict]
  congr 1
  ext ω
  exact escapeEvent_restrict_incident G hloc Λ x ω

theorem internal_edge_mem_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) {e : E} (he : e ∈ internalEdges G (S : Set V)) :
    e ∈ incidentSupport G hloc S := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G e)
  have ha : a ∈ G e := by rw [← hab]; simp
  exact (mem_incidentSupport G hloc S e).mpr ⟨a,he a ha,ha⟩

theorem internalSupport_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) :
    internalSupport G S F = internalSupport G S (incidentSupport G hloc S) := by
  ext e
  simp only [internalSupport,Finset.mem_filter]
  exact ⟨fun h => ⟨internal_edge_mem_incident G hloc S h.2,h.2⟩,
    fun h => ⟨hF h.1,h.2⟩⟩

theorem crossingCount_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) (ω : Set E) :
    crossingCount G S x F ω = crossingCount G S x (incidentSupport G hloc S) ω := by
  symm
  apply Finset.sum_subset hF
  intro e _ he
  have hn : ¬ crossingReach G S x ω e := by
    rintro ⟨a,b,hab,ha,_,_⟩
    exact he ((mem_incidentSupport G hloc S e).mpr ⟨a,ha,by simp [hab]⟩)
  simp [hn]

theorem boundaryExpectation_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) (p : ℝ) :
    boundaryExpectation G S x F p =
      boundaryExpectation G S x (incidentSupport G hloc S) p := by
  unfold boundaryExpectation
  rw [internalSupport_eq_of_incident_subset G hloc S F hF]
  apply bernoulliPolynomial_congr
  intro t _
  exact crossingCount_eq_of_incident_subset G hloc S x F hF t


theorem measurableSet_escapeEvent (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) : MeasurableSet (escapeEvent G Λ x) := by
  let F := incidentSupport G hloc Λ
  have he : escapeEvent G Λ x =
      (fun ω => (Subtype.val ⁻¹' ω : Set (F : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ escapeEvent G Λ x} := by
    ext ω
    have hh : Subtype.val '' (Subtype.val ⁻¹' ω : Set (F : Set E)) = ω ∩ (F : Set E) := by
      ext e
      simp [and_comm]
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hh]
    exact (escapeEvent_restrict_incident G hloc Λ x ω).symm
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem escapeEvent_antitone_domain (G : BondGraph V E) {S Λ : Set V} (hS : S ⊆ Λ)
    (x : V) : escapeEvent G Λ x ⊆ escapeEvent G S x := by
  intro ω hω hn
  apply hω
  intro y hxy
  exact hS (hn y hxy)

theorem vertexExhaustion_mono [Encodable V] :
    Monotone (vertexExhaustion : ℕ → Finset V) := by
  intro m n h x hx
  simp only [vertexExhaustion,Finset.mem_preimage,Finset.mem_range] at hx ⊢
  exact hx.trans_le h

theorem subset_vertexExhaustion [Encodable V] (S : Finset V) :
    ∃ n, S ⊆ vertexExhaustion n := by
  refine ⟨S.sup Encodable.encode+1,?_⟩
  intro x hx
  simp only [vertexExhaustion,Finset.mem_preimage,Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup hx)

theorem infinite_cluster_eq_iInter_escape [Encodable V] (G : BondGraph V E) (x : V) :
    {ω | (cluster G ω x).Infinite} = ⋂ n, escapeEvent G (vertexExhaustion (V := V) n : Set V) x := by
  ext ω
  simp only [Set.mem_ofPred_eq,Set.mem_iInter]
  constructor
  · intro hi n hn
    exact hi ((vertexExhaustion n).finite_toSet.subset (by
      intro y hy; exact hn y hy))
  · intro he hf
    obtain ⟨n,hn⟩ := subset_vertexExhaustion hf.toFinset
    apply he n
    intro y hy
    exact hn (hf.mem_toFinset.mpr hy)

 
theorem infinite_cluster_probability_ge_of_escape [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (p : unitInterval) (c : ℝ)
    (hc : ∀ Λ : Finset V, c ≤ (law p).real (escapeEvent G Λ x)) :
    c ≤ (law p).real {ω | (cluster G ω x).Infinite} := by
  let := Encodable.ofCountable V
  rw [infinite_cluster_eq_iInter_escape]
  have hm : Antitone (fun n => escapeEvent G (vertexExhaustion (V := V) n : Set V) x) := by
    intro m n h
    exact escapeEvent_antitone_domain G (by exact_mod_cast vertexExhaustion_mono h) x
  have ht := tendsto_measure_iInter_atTop (μ := law p)
    (fun n => (measurableSet_escapeEvent G hloc (vertexExhaustion n) x).nullMeasurableSet)
    hm ⟨0,measure_ne_top _ _⟩
  have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact ge_of_tendsto hr (Eventually.of_forall (fun n => hc (vertexExhaustion n)))

 

theorem infinite_cluster_probability_pos_of_bad_cost [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (r p : unitInterval)
    (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S : Finset V, x ∈ S → 1 ≤ boundaryCost G hloc S x (r : ℝ)) :
    0 < (law p).real {ω | (cluster G ω x).Infinite} := by
  have hc : 0 < 1-Real.exp ((r:ℝ)-(p:ℝ)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hrp))
  apply hc.trans_le
  apply infinite_cluster_probability_ge_of_escape G hloc x p
  intro Λ
  rw [← finite_escape_eq_law G hloc Λ x p]
  apply (finite_escape_probability_lower G Λ x (incidentSupport G hloc Λ)
    (r:ℝ) (p:ℝ) hr hrp hp ?_).2
  intro S hS hx
  rw [boundaryExpectation_eq_of_incident_subset G hloc S x _ (incidentSupport_mono G hloc hS)]
  exact hcost S hx

theorem pc_le_of_infinite_cluster_probability_pos (G : BondGraph V E)
    (x : V) (p : unitInterval) (hp : 0 < (law p).real {ω | (cluster G ω x).Infinite}) :
    pc G ≤ p := by
  apply sInf_le
  have hh : 0 < law p {ω | (cluster G ω x).Infinite} := (ENNReal.toReal_pos_iff.mp hp).1
  apply hh.trans_le
  apply measure_mono
  intro ω hω
  exact ⟨cluster G ω x,hω,x,rfl⟩

 
theorem exists_subcritical_testSet [Countable V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∃ S : Finset V, x ∈ S ∧ boundaryCost G hloc S x (p:ℝ) < 1 := by
  by_cases hz : p = 0
  · exact ⟨{x},by simp,by simp [hz,boundaryCost]⟩
  · have hp0 : 0 < p := bot_lt_iff_ne_bot.mpr hz
    by_contra! hn
    obtain ⟨q,hpq,hqc⟩ := exists_between hp
    have hq1 : q < 1 := hqc.trans_le (show pc G ≤ 1 from (pc G).2.2)
    have hs := infinite_cluster_probability_pos_of_bad_cost G hloc x p q hp0 hpq hq1 hn
    exact (not_le_of_gt hqc) (pc_le_of_infinite_cluster_probability_pos G x q hs)

theorem internalEdges_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (e : E) :
    b e ∈ internalEdges G (a '' S) ↔ e ∈ internalEdges G S := by
  constructor
  · intro he x hx
    have hh := he (a x) (by rw [h e]; exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩)
    simpa using hh
  · intro he y hy
    rw [h e,Sym2.mem_map] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact Set.mem_image_of_mem a (he x hx)

theorem crossingReach_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (ω : Set E) (e : E) :
    crossingReach G (a '' S) (a x) (b '' ω) (b e) ↔ crossingReach G S x ω e := by
  constructor
  · rintro ⟨c,d,he,hc,hd,hconn⟩
    have he' : G e = s(a.symm c,a.symm d) := by
      have hh := congrArg (Sym2.map a.symm) he
      rw [h e,Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id,Sym2.map_mk] at hh
      exact hh
    refine ⟨a.symm c,a.symm d,he',?_,?_,?_⟩
    · simpa using hc
    · simpa using hd
    · have hh := (conn_aut_iff G h (b '' ω) x (a.symm c)).mpr (by simpa using hconn)
      simpa only [Set.preimage_image_eq _ b.injective] using hh
  · rintro ⟨c,d,he,hc,hd,hconn⟩
    refine ⟨a c,a d,?_,by simpa using hc,by simpa using hd,conn_aut G h hconn⟩
    rw [h e,he,Sym2.map_mk]

theorem internalSupport_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (F : Finset E) :
    internalSupport G (a '' S) (F.map b.toEmbedding) =
      (internalSupport G S F).map b.toEmbedding := by
  ext e
  obtain ⟨d,rfl⟩ := b.surjective e
  simp [internalSupport,internalEdges_aut_iff G h]

theorem crossingCount_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (F : Finset E) (ω : Set E) :
    crossingCount G (a '' S) (a x) (F.map b.toEmbedding) (b '' ω) =
      crossingCount G S x F ω := by
  simp only [crossingCount,Finset.sum_map,Equiv.toEmbedding_apply,crossingReach_aut_iff G h]

theorem boundaryExpectation_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (F : Finset E) (p : ℝ) :
    boundaryExpectation G (a '' S) (a x) (F.map b.toEmbedding) p =
      boundaryExpectation G S x F p := by
  unfold boundaryExpectation
  rw [internalSupport_aut G h,bernoulliPolynomial_map]
  apply bernoulliPolynomial_congr
  intro t _
  simp only [Finset.coe_map,Equiv.coe_toEmbedding]
  exact crossingCount_aut G h S x F t

theorem boundaryCost_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (S : Finset V) (x : V) (p : ℝ) :
    boundaryCost G hloc (S.map a.toEmbedding) (a x) p = boundaryCost G hloc S x p := by
  unfold boundaryCost
  rw [incidentSupport_aut G hloc h,Finset.coe_map]
  exact congrArg (p*·) (boundaryExpectation_aut G h S x (incidentSupport G hloc S) p)

 

theorem exists_uniform_subcritical_testSets [Countable V] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) :
    ∃ (L : ℕ) (a : ℝ), 0 ≤ a ∧ a < 1 ∧ ∀ x, ∃ S : Finset V,
      x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p:ℝ) ≤ a := by
  obtain ⟨O,hO⟩ := hqt
  choose S hmem hcost using exists_subcritical_testSet G hloc p hp
  have hOn : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO (Classical.arbitrary V)
    exact ⟨o,ho⟩
  let L := O.sup (fun x => (S x).card)
  let a := max 0 (O.sup' hOn (fun x => boundaryCost G hloc (S x) x (p:ℝ)))
  refine ⟨L,a,le_max_left _ _,?_,?_⟩
  · apply max_lt zero_lt_one
    exact (Finset.sup'_lt_iff hOn).mpr (fun x _ => hcost x)
  · intro x
    obtain ⟨o,ho,α,β,hαβ,rfl⟩ := hO x
    refine ⟨(S o).map α.toEmbedding,?_,?_,?_⟩
    · simp only [Finset.mem_map,Equiv.toEmbedding_apply]
      exact ⟨o,hmem o,rfl⟩
    · simpa only [Finset.card_map] using Finset.le_sup (f := fun x => (S x).card) ho
    · rw [boundaryCost_aut G hloc hαβ]
      exact (Finset.le_sup' (f := fun x => boundaryCost G hloc (S x) x (p:ℝ)) ho).trans
        (le_max_right _ _)

end SharpnessBridge

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq


theorem cut_spec [Nonempty V] (G : BondGraph V E) (S : Set V) {e : E}
    (he : CutExists G S e) :
    G e = s(cutInside G S e,cutOutside G S e) ∧
      cutInside G S e ∈ S ∧ cutOutside G S e ∉ S := by
  simpa only [cutInside,cutOutside,dite_eq_left he] using he.choose_spec.choose_spec

theorem cut_unique [Nonempty V] (G : BondGraph V E) (S : Set V) {e : E} {a b : V}
    (he : G e = s(a,b)) (ha : a ∈ S) (hb : b ∉ S) :
    a = cutInside G S e ∧ b = cutOutside G S e := by
  have hc := cut_spec G S (e := e) ⟨a,b,he,ha,hb⟩
  have hh := Sym2.eq_iff.mp (he.symm.trans hc.1)
  rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨h₁,h₂⟩
  · exact (hc.2.2 (h₁ ▸ ha)).elim

theorem crossingReach_upper (G : BondGraph V E) (S : Set V) (x : V) (e : E) :
    IsUpperSet {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  rintro ω η h ⟨a,b,he,ha,hb,hconn⟩
  exact ⟨a,b,he,ha,hb,conn_mono G (Set.inter_subset_inter_left _ h) hconn⟩

theorem finiteWitness_crossingReach (G : BondGraph V E) (S : Set V) (x : V) (e : E) :
    FiniteWitness {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  rintro ω ⟨a,b,he,ha,hb,hconn⟩
  obtain ⟨t,ht,hc⟩ := finiteWitness_inter {η | Conn G η x a} (finiteWitness_conn G x a)
    (internalEdges G S) ω hconn
  exact ⟨t,ht,a,b,he,ha,hb,hc⟩

 
theorem conn_first_exit [Nonempty V] (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (U : Set E) {ω : Set E} {x y : V} (hx : x ∈ S)
    (hxy : Conn G (ω ∩ U) x y) :
    y ∈ S ∨ ∃ e ∈ incidentSupport G hloc S,
      ω ∈ DisjointOccurrence {η | crossingReach G S x (η ∩ internalEdges G S) e}
        (DisjointOccurrence {η | e ∈ η} {η | Conn G (η ∩ U) (cutOutside G S e) y}) := by
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G hxy
  rcases hl.first_outside (internalEdges G S) with hall |
      ⟨a,b,e,l₁,l₂,heq,h₁,he,h₂,hfirst,hnot⟩
  · exact Or.inl (conn_internal_endpoint G S hx (hl.conn fun e he => ⟨(ho e he).1,hall e he⟩))
  · subst l
    have hnod := List.nodup_append.mp hn
    have hen : e ∉ l₂ := (List.nodup_cons.mp hnod.2.1).1
    have ha : a ∈ S := conn_internal_endpoint G S hx
      (h₁.conn (ω := ω ∩ internalEdges G S) fun d hd =>
        ⟨(ho d (List.mem_append_left _ hd)).1,hfirst d hd⟩)
    have hb : b ∉ S := fun hb => hnot ((mem_internalEdges_of_ends G S e a b he).mpr ⟨ha,hb⟩)
    have hbe := (cut_unique G S he ha hb).2
    refine Or.inr ⟨e,(mem_incidentSupport G hloc S e).mpr ⟨a,ha,by simp [he]⟩,
      l₁.toFinset,(e::l₂).toFinset,?_,?_,?_,?_,?_⟩
    · intro d hd
      exact (ho d (List.mem_append_left _ (List.mem_toFinset.mp hd))).1
    · intro d hd
      exact (ho d (List.mem_append_right _ (List.mem_toFinset.mp hd))).1
    · apply Finset.disjoint_left.mpr
      intro d hd hd'
      exact hnod.2.2 d (List.mem_toFinset.mp hd) d (List.mem_toFinset.mp hd') rfl
    · exact ⟨a,b,he,ha,hb,h₁.conn (fun d hd => ⟨by simpa using hd,hfirst d hd⟩)⟩
    · refine ⟨{e},l₂.toFinset,by simp,by simp,by simpa using hen,by simp,?_⟩
      rw [← hbe]
      exact h₂.conn fun d hd => ⟨by simpa using hd,
        (ho d (List.mem_append_right _ (List.mem_cons_of_mem e hd))).2⟩

 
theorem boundaryExpectation_eq_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (p : unitInterval) :
    boundaryExpectation G S x (incidentSupport G hloc S) (p:ℝ) =
      ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  have hI : (internalSupport G S (incidentSupport G hloc S) : Set E) = internalEdges G S := by
    ext e
    simp only [Finset.mem_coe,internalSupport,Finset.mem_filter]
    exact ⟨And.right,fun he => ⟨internal_edge_mem_incident G hloc S he,he⟩⟩
  unfold boundaryExpectation crossingCount bernoulliPolynomial
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  change finiteEventPolynomial (internalSupport G S (incidentSupport G hloc S))
    {ω | crossingReach G S x ω e} (p:ℝ) = _
  rw [finiteEventPolynomial_restrict,hI]
  rfl

 
theorem domainTwoPoint_first_exit [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Finset V) (Λ : Set V) (p : unitInterval)
    (x y : V) (hx : x ∈ S) :
    domainTwoPoint G Λ p x y ≤ (if y ∈ S then (1:ℝ) else 0) +
      ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
          (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y := by
  by_cases hy : y ∈ S
  · have hnon : 0 ≤ ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
          (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y := by
      apply Finset.sum_nonneg
      intro e _
      exact mul_nonneg (mul_nonneg (measureReal_nonneg) p.2.1) measureReal_nonneg
    simpa only [ite_eq_left hy,domainTwoPoint] using (measureReal_le_one (μ := law p)
      (s := {ω | Conn G (ω ∩ internalEdges G Λ) x y})).trans (le_add_of_nonneg_right hnon)
  · simp only [ite_eq_right hy,zero_add]
    let A := fun e => {ω | crossingReach G S x (ω ∩ internalEdges G S) e}
    let B := fun e => {ω | Conn G (ω ∩ internalEdges G Λ) (cutOutside G S e) y}
    let F := incidentSupport G hloc S
    let C := fun e => DisjointOccurrence (A e) (DisjointOccurrence {ω | e ∈ ω} (B e))
    have hsub : {ω | Conn G (ω ∩ internalEdges G Λ) x y} ⊆ ⋃ e ∈ F, C e := by
      intro ω hω
      rcases conn_first_exit G hloc S (internalEdges G Λ) hx hω with h | ⟨e,he,h⟩
      · exact (hy h).elim
      · exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨he,h⟩⟩
    calc
      domainTwoPoint G Λ p x y ≤ (law p).real (⋃ e ∈ F, C e) := measureReal_mono (μ := law p) hsub (measure_ne_top _ _)
      _ ≤ ∑ e ∈ F, (law p).real (C e) := measureReal_biUnion_finset_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro e _
        have hB : IsUpperSet (B e) := fun _ _ h hc =>
          conn_mono G (Set.inter_subset_inter_left _ h) hc
        have hfB : FiniteWitness (B e) := finiteWitness_inter _
          (finiteWitness_conn G _ _) (internalEdges G Λ)
        have hb := bk p (A e) (DisjointOccurrence {ω | e ∈ ω} (B e))
          (crossingReach_upper G S x e) (disjointOccurrence_upper _ _)
          (finiteWitness_crossingReach G S x e) (finiteWitness_disjointOccurrence _ _)
        have hb' := bk p {ω | e ∈ ω} (B e) (fun _ _ h he => h he) hB (finiteWitness_edge e) hfB
        have heq : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
          simpa using finite_open_probability p {e}
        rw [heq] at hb'
        calc
          (law p).real (C e) ≤ (law p).real (A e) * (law p).real
              (DisjointOccurrence {ω | e ∈ ω} (B e)) := hb
          _ ≤ (law p).real (A e) * ((p:ℝ) * (law p).real (B e)) :=
            mul_le_mul_of_nonneg_left hb' measureReal_nonneg
          _ = _ := (mul_assoc _ _ _).symm

theorem conn_internal_eq_or_mem (G : BondGraph V E) (S : Set V) {ω : Set E} {x y : V}
    (h : Conn G (ω ∩ internalEdges G S) x y) : x = y ∨ x ∈ S ∧ y ∈ S := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    have he' := (mem_internalEdges_of_ends G S e a b heq).mp he.2
    right
    exact ⟨ih.elim (fun h => h.symm ▸ he'.1) And.left,he'.2⟩

theorem domainTwoPoint_zero_of_outside (G : BondGraph V E) (S : Set V) (p : unitInterval)
    {x y : V} (hx : x ∉ S) (hy : y ∈ S) : domainTwoPoint G S p x y = 0 := by
  have he : {ω | Conn G (ω ∩ internalEdges G S) x y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω h
    rcases conn_internal_eq_or_mem G S h with rfl | h
    · exact hx hy
    · exact hx h.1
  simp only [domainTwoPoint,he,measureReal_empty]

theorem domainRow_le_boundaryCost [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (S Λ : Finset V) (p : unitInterval) (x : V) (hx : x ∈ S)
    (H : ℝ) (hH : ∀ z, ∑ y ∈ Λ, domainTwoPoint G Λ p z y ≤ H) :
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤ S.card + boundaryCost G hloc S x (p:ℝ) * H := by
  have hind : (∑ y ∈ Λ, if y ∈ S then (1:ℝ) else 0) ≤ (S.card:ℝ) := by
    simp only [← Finset.sum_filter]
    simpa using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card
      (show Λ.filter (fun y => y ∈ S) ⊆ S from fun y hy => (Finset.mem_filter.mp hy).2))
  calc
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤
        ∑ y ∈ Λ, ((if y ∈ S then (1:ℝ) else 0) +
          ∑ e ∈ incidentSupport G hloc S,
            (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
              (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y) :=
      Finset.sum_le_sum fun y _ => domainTwoPoint_first_exit G hloc S Λ p x y hx
    _ = (∑ y ∈ Λ, if y ∈ S then (1:ℝ) else 0) +
        ∑ e ∈ incidentSupport G hloc S,
          (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
            (p:ℝ) * ∑ y ∈ Λ, domainTwoPoint G Λ p (cutOutside G S e) y := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [← Finset.mul_sum]
    _ ≤ S.card + ∑ e ∈ incidentSupport G hloc S,
          (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} * (p:ℝ) * H := by
      apply add_le_add hind
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (hH _) (mul_nonneg measureReal_nonneg p.2.1)
    _ = S.card + boundaryCost G hloc S x (p:ℝ) * H := by
      unfold boundaryCost
      rw [boundaryExpectation_eq_sum]
      simp only [← Finset.sum_mul]
      ring

theorem domainRow_uniform_bound [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (p : unitInterval) (L : ℕ) (a : ℝ) (ha : a < 1)
    (htest : ∀ x, ∃ S : Finset V, x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p:ℝ) ≤ a)
    (Λ : Finset V) (x : V) :
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤ (L:ℝ)/(1-a) := by
  by_cases hΛ : Λ.Nonempty
  · let row := fun z => ∑ y ∈ Λ, domainTwoPoint G Λ p z y
    obtain ⟨z,hz,hmax⟩ := Λ.exists_max_image row hΛ
    have hnon : 0 ≤ row z := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
    have hH : ∀ w, row w ≤ row z := by
      intro w
      by_cases hw : w ∈ Λ
      · exact hmax w hw
      · have he : row w = 0 := by
          apply Finset.sum_eq_zero
          intro y hy
          exact domainTwoPoint_zero_of_outside G Λ p hw hy
        rwa [he]
    obtain ⟨S,hS,hcard,hcost⟩ := htest z
    have h := domainRow_le_boundaryCost G hloc S Λ p z hS (row z) hH
    have hL : (S.card:ℝ) ≤ (L:ℝ) := Nat.cast_le.mpr hcard
    have hc := mul_le_mul_of_nonneg_right hcost hnon
    have hrow : row z ≤ (L:ℝ)/(1-a) := (le_div_iff₀ (sub_pos.mpr ha)).mpr (by nlinarith)
    exact (hH x).trans hrow
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hΛ,Finset.sum_empty]
    exact div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr ha).le

theorem internalEdges_mono (G : BondGraph V E) {S T : Set V} (h : S ⊆ T) :
    internalEdges G S ⊆ internalEdges G T := fun _ he x hx => h (he x hx)

theorem exists_internal_vertexExhaustion [Encodable V] (G : BondGraph V E) (e : E) :
    ∃ n, e ∈ internalEdges G (vertexExhaustion (V := V) n : Set V) := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G e)
  obtain ⟨n,hn⟩ := subset_vertexExhaustion ({a,b} : Finset V)
  refine ⟨n,?_⟩
  rw [mem_internalEdges_of_ends G _ e a b hab.symm]
  exact ⟨hn (by simp),hn (by simp)⟩

theorem conn_domain_exhaustion [Encodable V] (G : BondGraph V E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    ∃ n, Conn G (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y := by
  induction h with
  | refl => exact ⟨0,conn_refl _ _ _⟩
  | @tail a b hxa hab ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨e,he,heq⟩ := hab
    obtain ⟨m,hm⟩ := exists_internal_vertexExhaustion G e
    refine ⟨max n m,?_⟩
    have hnm := internalEdges_mono G (show (vertexExhaustion (V := V) n : Set V) ⊆
        (vertexExhaustion (V := V) (max n m) : Set V) from vertexExhaustion_mono (le_max_left n m))
    have hmm := internalEdges_mono G (show (vertexExhaustion (V := V) m : Set V) ⊆
        (vertexExhaustion (V := V) (max n m) : Set V) from vertexExhaustion_mono (le_max_right n m))
    exact (conn_mono G (Set.inter_subset_inter_right _ hnm) hn).tail ⟨e,⟨he,hmm hm⟩,heq⟩

theorem tendsto_domainTwoPoint [Encodable V] (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Tendsto (fun n => domainTwoPoint G (vertexExhaustion (V := V) n : Set V) p x y)
      atTop (𝓝 (twoPoint G p x y)) := by
  have hm : Monotone (fun n => {ω | Conn G
      (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y}) := by
    intro m n h ω hc
    exact conn_mono G (Set.inter_subset_inter_right _ (internalEdges_mono G
      (show (vertexExhaustion (V := V) m : Set V) ⊆ (vertexExhaustion (V := V) n : Set V) from
        vertexExhaustion_mono h))) hc
  have he : (⋃ n, {ω | Conn G (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y}) =
      {ω | Conn G ω x y} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,h⟩ => conn_mono G Set.inter_subset_left h,conn_domain_exhaustion G⟩
  have h := tendsto_measure_iUnion_atTop (μ := law p) hm
  rw [he] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

 
theorem subcritical_row_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x (F : Finset V), ∑ y ∈ F, twoPoint G p x y ≤ C := by
  let : Encodable V := Encodable.ofCountable V
  obtain ⟨L,a,_,ha,htest⟩ := exists_uniform_subcritical_testSets G hloc hqt p hp
  refine ⟨(L:ℝ)/(1-a),div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr ha).le,?_⟩
  intro x F
  apply le_of_tendsto (tendsto_finsetSum F (fun y _ => tendsto_domainTwoPoint G p x y))
  obtain ⟨N,hN⟩ := subset_vertexExhaustion F
  filter_upwards [eventually_ge_atTop N] with n hn
  have hFn : F ⊆ vertexExhaustion n := hN.trans (vertexExhaustion_mono hn)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hFn (fun _ _ _ => measureReal_nonneg)).trans
    (domainRow_uniform_bound G hloc p L a ha htest (vertexExhaustion n) x)


end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Marked
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked decision trees, graph searches and pivotal geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedExploration


namespace ProbeTree

lemma weight_nonneg (p h : unitInterval) (t : ProbeTree) (l : t.Leaf) :
    0 ≤ weight p h t l := by
  induction t with
  | done b => exact zero_le_one
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_nonneg (sub_nonneg.mpr p.2.2) (ih₀ l)
    | inr l => exact mul_nonneg p.2.1 (ih₁ l)
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_nonneg (sub_nonneg.mpr h.2.2) (ih₀ l)
    | inr l => exact mul_nonneg h.2.1 (ih₁ l)

lemma sum_weight (p h : ℝ) (t : ProbeTree) : ∑ l, weight p h t l = 1 := by
  induction t with
  | done b => change (∑ _ : Unit, (1:ℝ)) = 1; simp
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 1
    simp only [Fintype.sum_sum_type,weight,← Finset.mul_sum,ih₀,ih₁]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 1
    simp only [Fintype.sum_sum_type,weight,← Finset.mul_sum,ih₀,ih₁]
    ring


lemma successWeight_nonneg (p h : unitInterval) (t : ProbeTree) (l : t.Leaf) :
    0 ≤ successWeight p h t l := by
  unfold successWeight
  split <;> simp_all [weight_nonneg]

lemma successMass_nonneg (p h : unitInterval) (t : ProbeTree) : 0 ≤ successMass p h t :=
  Finset.sum_nonneg fun _ _ => successWeight_nonneg p h t _

lemma successMass_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMass p h (.edge t₀ t₁) = (1-p)*successMass p h t₀+p*successMass p h t₁ := by
  simp only [successMass,Fintype.sum_sum_type,successWeight,outcome,weight,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split <;> simp

lemma successMass_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMass p h (.mark t₀ t₁) = (1-h)*successMass p h t₀+h*successMass p h t₁ := by
  simp only [successMass,Fintype.sum_sum_type,successWeight,outcome,weight,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split <;> simp

end ProbeTree
end MarkedExploration

section LabelledExploration
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace LabelledTree

theorem eval_congr (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {ω ω' : Finset E} {m m' : Finset V}
    (hω : ∀ e ∈ Q, e ∈ ω ↔ e ∈ ω') (hm : ∀ v ∈ F, v ∈ m ↔ v ∈ m') :
    t.eval ω m = t.eval ω' m' := by
  induction t generalizing Q F with
  | done b => rfl
  | edge e t₀ t₁ ih₀ ih₁ =>
    obtain ⟨he,h₀,h₁⟩ := ht
    simp only [eval,hω e he]
    split
    · exact ih₁ h₁ (fun a ha => hω a (Finset.mem_of_mem_erase ha)) hm
    · exact ih₀ h₀ (fun a ha => hω a (Finset.mem_of_mem_erase ha)) hm
  | mark v t₀ t₁ ih₀ ih₁ =>
    obtain ⟨hv,h₀,h₁⟩ := ht
    simp only [eval,hm v hv]
    split
    · exact ih₁ h₁ hω (fun a ha => hm a (Finset.mem_of_mem_erase ha))
    · exact ih₀ h₀ hω (fun a ha => hm a (Finset.mem_of_mem_erase ha))

lemma eval_insert_edge (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {e : E} (he : e ∉ Q) (ω : Finset E) (m : Finset V) :
    t.eval (insert e ω) m = t.eval ω m := by
  apply eval_congr t ht
  · intro a ha
    simp [show a ≠ e from fun hh => he (hh ▸ ha)]
  · simp

lemma eval_insert_mark (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {v : V} (hv : v ∉ F) (ω : Finset E) (m : Finset V) :
    t.eval ω (insert v m) = t.eval ω m := by
  apply eval_congr t ht
  · simp
  · intro a ha
    simp [show a ≠ v from fun hh => hv (hh ▸ ha)]

end LabelledTree

theorem bernoulliPolynomial_affine (s : Finset E) (f g : Finset E → ℝ) (a b p : ℝ) :
    bernoulliPolynomial s (fun t => a*f t+b*g t) p =
      a*bernoulliPolynomial s f p+b*bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> ring

namespace LabelledTree

 
theorem expectation_eq (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) (p h : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial F
      (fun m => if t.eval ω m then 1 else 0) h) p =
      ProbeTree.successMass p h t.forget := by
  induction t generalizing Q F with
  | done b =>
    cases b <;> simp [eval,forget,ProbeTree.successMass_done,bernoulliPolynomial_const]
  | edge e t₀ t₁ ih₀ ih₁ =>
    obtain ⟨he,h₀,h₁⟩ := ht
    conv_lhs => rw [← Finset.insert_erase he]
    rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
    have hc : bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if (edge e t₀ t₁).eval ω m then 1 else 0) h) p =
        bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if t₀.eval ω m then 1 else 0) h) p := by
      apply bernoulliPolynomial_congr
      intro ω hω
      have heω : e ∉ ω := fun hh => Finset.notMem_erase e Q (hω hh)
      simp only [eval,heω,if_false]
    have ho : bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if (edge e t₀ t₁).eval (insert e ω) m then 1 else 0) h) p =
        bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if t₁.eval ω m then 1 else 0) h) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      simp only [eval,Finset.mem_insert_self,if_true]
      apply bernoulliPolynomial_congr
      intro m _
      rw [eval_insert_edge t₁ h₁ (Finset.notMem_erase e Q)]
    rw [hc,ho,ih₀ h₀,ih₁ h₁,forget,ProbeTree.successMass_edge]
  | mark v t₀ t₁ ih₀ ih₁ =>
    obtain ⟨hv,h₀,h₁⟩ := ht
    have hh : ∀ ω, bernoulliPolynomial F
        (fun m => if (mark v t₀ t₁).eval ω m then 1 else 0) h =
      (1-h)*bernoulliPolynomial (F.erase v) (fun m => if t₀.eval ω m then 1 else 0) h +
        h*bernoulliPolynomial (F.erase v) (fun m => if t₁.eval ω m then 1 else 0) h := by
      intro ω
      conv_lhs => rw [← Finset.insert_erase hv]
      rw [bernoulliPolynomial_insert _ v (Finset.notMem_erase v F)]
      congr 1
      · congr 1
        apply bernoulliPolynomial_congr
        intro m hm
        have hvm : v ∉ m := fun hh => Finset.notMem_erase v F (hm hh)
        simp only [eval,hvm,if_false]
      · congr 1
        apply bernoulliPolynomial_congr
        intro m _
        simp only [eval,Finset.mem_insert_self,if_true]
        rw [eval_insert_mark t₁ h₁ (Finset.notMem_erase v F)]
    simp_rw [hh]
    rw [bernoulliPolynomial_affine,ih₀ h₀,ih₁ h₁,forget,ProbeTree.successMass_mark]

end LabelledTree
end LabelledExploration

section GraphMarkedSearch
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem searchCrossing_spec (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : SearchCrossing G Q R) :
    (searchCrossing G Q R h).1 ∈ Q ∧ (searchCrossing G Q R h).2.1 ∈ R ∧
      (searchCrossing G Q R h).2.2 ∉ R ∧
      G (searchCrossing G Q R h).1 = s((searchCrossing G Q R h).2.1,(searchCrossing G Q R h).2.2) :=
  Classical.choose_spec h


lemma searchAvailable_erase (G : BondGraph V E) {Q : Finset E} {R F : Finset V}
    (h : SearchAvailable G Q R F) (e : E) : SearchAvailable G (Q.erase e) R F :=
  fun _ ha _ hv => h _ (Finset.mem_of_mem_erase ha) _ hv

lemma searchAvailable_discover (G : BondGraph V E) {Q : Finset E} {R F : Finset V}
    (h : SearchAvailable G Q R F) (e : E) (v : V) :
    SearchAvailable G (Q.erase e) (insert v R) (F.erase v) := by
  intro a ha b hb
  rcases h a (Finset.mem_of_mem_erase ha) b hb with hb | hb
  · exact Or.inl (Finset.mem_insert_of_mem hb)
  · by_cases hbe : b = v
    · exact Or.inl (by simp [hbe])
    · exact Or.inr (Finset.mem_erase.mpr ⟨hbe,hb⟩)

theorem clusterSearch_valid (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R F : Finset V)
    (ha : SearchAvailable G Q R F) : LabelledTree.Valid Q F (clusterSearch G n Q R) := by
  induction n generalizing Q R F with
  | zero => trivial
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      refine ⟨he,ih _ _ _ (searchAvailable_erase G ha _),?_,?_,trivial⟩
      · exact (ha _ he _ (by rw [hends]; simp)).resolve_left hw
      · exact ih _ _ _ (searchAvailable_discover G ha _ _)
    · trivial

theorem clusterSearch_markSearch (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V) :
    ProbeTree.IsMarkSearch (clusterSearch G n Q R).forget := by
  induction n generalizing Q R with
  | zero => exact .fail
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs
    · exact .edge (ih _ _) (.mark (ih _ _))
    · exact .fail


theorem seedMarked_insert_edge (G : BondGraph V E) (ω : Set E) (R m : Finset V)
    (e : E) (a b : V) (ha : a ∈ R) (he : G e = s(a,b)) :
    SeedMarked G (insert e ω) R m ↔ SeedMarked G ω (insert b R) m := by
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | ⟨_,h⟩ | ⟨_,h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hx,y,hy,h⟩
    · exact ⟨b,by simp,y,hy,h⟩
    · exact ⟨a,Finset.mem_insert_of_mem ha,y,hy,h⟩
  · rintro ⟨x,hx,y,hy,hxy⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · refine ⟨a,ha,y,hy,?_⟩
      exact (Relation.ReflTransGen.single ⟨e,Set.mem_insert e ω,he⟩).trans
        (conn_mono G (Set.subset_insert e ω) hxy)
    · exact ⟨x,hx,y,hy,conn_mono G (Set.subset_insert e ω) hxy⟩

theorem seedMarked_false_of_no_crossing (G : BondGraph V E) (Q : Finset E) (R m : Finset V)
    (hc : ¬ SearchCrossing G Q R) (hm : Disjoint R m) (ω : Finset E) (hω : ω ⊆ Q) :
    ¬ SeedMarked G (ω : Set E) R m := by
  rintro ⟨a,ha,b,hb,hab⟩
  have hclosed : ∀ x ∈ R, ∀ y, Conn G (ω : Set E) x y → y ∈ R := by
    intro x hx y hxy
    induction hxy with
    | refl => exact hx
    | @tail v w hv hw ih =>
      by_contra hn
      obtain ⟨e,he,hevw⟩ := hw
      exact hc ⟨(e,v,w),hω he,ih,hn,hevw⟩
  exact Finset.disjoint_left.mp hm (hclosed a ha b hab) hb

 
theorem clusterSearch_correct (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R F m : Finset V)
    (hn : Q.card ≤ n) (ha : SearchAvailable G Q R F) (hm : Disjoint R m)
    (ω : Finset E) (hω : ω ⊆ Q) :
    (clusterSearch G n Q R).eval ω m = true ↔ SeedMarked G (ω : Set E) R m := by
  induction n generalizing Q R F ω with
  | zero =>
    have hQ : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    have hωe : ω = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by simp_all)
    simp only [clusterSearch,LabelledTree.eval,Bool.false_eq_true,false_iff]
    exact seedMarked_false_of_no_crossing G Q R m (by simp [SearchCrossing,hQ]) hm ω hω
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      have hcard : (Q.erase (searchCrossing G Q R hc).1).card ≤ n := by
        rw [Finset.card_erase_of_mem he]; omega
      simp only [LabelledTree.eval]
      by_cases heω : (searchCrossing G Q R hc).1 ∈ ω
      · simp only [heω,if_true]
        rw [← Finset.insert_erase heω,Finset.coe_insert,
          seedMarked_insert_edge G _ R m _ _ _ hv hends]
        by_cases hwm : (searchCrossing G Q R hc).2.2 ∈ m
        · simp only [hwm,if_true,true_iff]
          exact ⟨_,by simp,_,hwm,conn_refl G _ _⟩
        · simp only [hwm,if_false]
          rw [LabelledTree.eval_insert_edge _
            (clusterSearch_valid G n _ _ (F.erase (searchCrossing G Q R hc).2.2)
              (searchAvailable_discover G ha _ _)) (Finset.notMem_erase _ _)]
          exact ih _ _ _ hcard (searchAvailable_discover G ha _ _)
            (Finset.disjoint_insert_left.mpr ⟨hwm,hm⟩) (ω.erase (searchCrossing G Q R hc).1)
            (Finset.erase_subset_erase _ hω)
      · simp only [heω,if_false]
        exact ih _ _ _ hcard (searchAvailable_erase G ha _ ) hm ω
          (fun e he => Finset.mem_erase.mpr ⟨fun heq => heω (heq ▸ he),hω he⟩)
    · simp only [false_iff]
      exact seedMarked_false_of_no_crossing G Q R m hc hm ω hω

end GraphMarkedSearch

section GraphSearchCost
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace ProbeTree

lemma budget_done (b : Bool) (K d : ℕ) : Budget (.done b) K d := by
  intro l
  simp [queries,marks]

lemma budget_mono {t : ProbeTree} {K L d : ℕ} (h : Budget t K d) (hKL : K ≤ L) :
    Budget t L d := fun l => (h l).trans (Nat.add_le_add_right hKL _)

lemma budget_edge {t₀ t₁ : ProbeTree} {K d : ℕ} (h₀ : Budget t₀ K d) (h₁ : Budget t₁ K d) :
    Budget (.edge t₀ t₁) (K+1) d := by
  intro l
  cases l with
  | inl l => simpa [queries,marks,Nat.add_right_comm] using Nat.add_le_add_right (h₀ l) 1
  | inr l => simpa [queries,marks,Nat.add_right_comm] using Nat.add_le_add_right (h₁ l) 1

lemma budget_mark {t₀ t₁ : ProbeTree} {K d : ℕ}
    (h₀ : Budget t₀ (K+d) d) (h₁ : Budget t₁ (K+d) d) :
    Budget (.mark t₀ t₁) K d := by
  intro l
  cases l with
  | inl l => simpa [queries,marks,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₀ l
  | inr l => simpa [queries,marks,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₁ l

end ProbeTree


lemma queryPotential_erase (G : BondGraph V E) (Q : Finset E) (R : Finset V) (e : E) :
    queryPotential G (Q.erase e) R = (queryPotential G Q R).erase e := by
  ext a
  simp [queryPotential,and_assoc]

lemma queryPotential_insert (G : BondGraph V E) (Q : Finset E) (R : Finset V) (v : V) :
    queryPotential G Q (insert v R) = queryPotential G Q R ∪ Q.filter (fun e => v ∈ G e) := by
  ext a
  simp [queryPotential,and_or_left,or_comm]

lemma filtered_degree_erase (G : BondGraph V E) (Q : Finset E) (d : ℕ)
    (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) (a : E) :
    ∀ v, ((Q.erase a).filter (fun e => v ∈ G e)).card ≤ d := by
  intro v
  apply (Finset.card_le_card ?_).trans (hd v)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_filter.mp he).1,
    (Finset.mem_filter.mp he).2⟩

lemma queryPotential_discover_card (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (e : E) (v : V) (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    (queryPotential G (Q.erase e) (insert v R)).card ≤
      ((queryPotential G Q R).erase e).card+d := by
  rw [queryPotential_insert,queryPotential_erase]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (filtered_degree_erase G Q d hd e v) _)

 
theorem clusterSearch_budget (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V)
    (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    ProbeTree.Budget (clusterSearch G n Q R).forget (queryPotential G Q R).card d := by
  induction n generalizing Q R with
  | zero => exact ProbeTree.budget_done _ _ _
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      have hpot : (searchCrossing G Q R hc).1 ∈ queryPotential G Q R := by
        exact Finset.mem_filter.mpr ⟨he,_,hv,by rw [hends]; simp⟩
      have hpos : 0 < (queryPotential G Q R).card := Finset.card_pos.mpr ⟨_,hpot⟩
      have hclosed := ih (Q.erase (searchCrossing G Q R hc).1) R
        (filtered_degree_erase G Q d hd _)
      have hopen := ih (Q.erase (searchCrossing G Q R hc).1)
        (insert (searchCrossing G Q R hc).2.2 R) (filtered_degree_erase G Q d hd _)
      rw [queryPotential_erase,Finset.card_erase_of_mem hpot] at hclosed
      have hnew := queryPotential_discover_card G Q R (searchCrossing G Q R hc).1
        (searchCrossing G Q R hc).2.2 d hd
      rw [Finset.card_erase_of_mem hpot] at hnew
      have hh := ProbeTree.budget_edge hclosed
        (ProbeTree.budget_mark (ProbeTree.budget_mono hopen hnew) (ProbeTree.budget_done true _ _))
      have hcadd : (queryPotential G Q R).card-1+1 = (queryPotential G Q R).card := by omega
      simpa only [LabelledTree.forget,hcadd] using hh
    · exact ProbeTree.budget_done _ _ _

lemma mem_searchVertices (G : BondGraph V E) {Q : Finset E} {e : E} (he : e ∈ Q)
    {v : V} (hv : v ∈ G e) : v ∈ searchVertices G Q :=
  Finset.mem_biUnion.mpr ⟨e,he,Sym2.mem_toFinset.mpr hv⟩

lemma markedClusterTree_available (G : BondGraph V E) (Q : Finset E) (x : V) :
    SearchAvailable G Q {x} ((insert x (searchVertices G Q)).erase x) := by
  intro e he v hv
  by_cases hx : v = x
  · exact Or.inl (by simpa using hx)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hx,Finset.mem_insert_of_mem (mem_searchVertices G he hv)⟩)

theorem markedClusterTree_valid (G : BondGraph V E) (Q : Finset E) (x : V) :
    LabelledTree.Valid Q (insert x (searchVertices G Q)) (markedClusterTree G Q x) :=
  ⟨by simp,clusterSearch_valid G _ _ _ _ (markedClusterTree_available G Q x),trivial⟩

theorem markedClusterTree_budget (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    ProbeTree.Budget (markedClusterTree G Q x).forget 0 d := by
  have hh := clusterSearch_budget G Q.card Q {x} d hd
  have hcost : (queryPotential G Q {x}).card ≤ 0+d := by simpa [queryPotential] using hd x
  exact ProbeTree.budget_mark (ProbeTree.budget_mono hh hcost) (ProbeTree.budget_done true _ _)

theorem markedClusterTree_correct (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (hω : ω ⊆ Q) (m : Finset V) :
    (markedClusterTree G Q x).eval ω m = true ↔ ∃ y ∈ m, Conn G (ω : Set E) x y := by
  simp only [markedClusterTree,LabelledTree.eval]
  by_cases hxm : x ∈ m
  · simp only [hxm,if_true,true_iff]
    exact ⟨x,hxm,conn_refl G _ x⟩
  · simp only [hxm,if_false]
    rw [clusterSearch_correct G Q.card Q {x} ((insert x (searchVertices G Q)).erase x) m
      le_rfl (markedClusterTree_available G Q x) (by simpa) ω hω]
    simp only [SeedMarked,Finset.mem_singleton,exists_eq_left]

end GraphSearchCost

section MarkedFirstMoment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem markedConnectionPolynomial_eq_tree (G : BondGraph V E) (Q : Finset E)
    (x : V) (h p : ℝ) :
    markedConnectionPolynomial G Q x h p =
      ProbeTree.successMass p h (markedClusterTree G Q x).forget := by
  rw [← LabelledTree.expectation_eq _ (markedClusterTree_valid G Q x) p h]
  apply bernoulliPolynomial_congr
  intro ω hω
  apply bernoulliPolynomial_congr
  intro m _
  simp only [markedClusterTree_correct G Q x ω hω m]

theorem bernoulliPolynomial_open_difference (s : Finset E) (e : E) (he : e ∈ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => if e ∈ t then f t-f (t.erase e) else 0) p =
      p*bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e s)]
  have hclosed : bernoulliPolynomial (s.erase e)
      (fun t => if e ∈ t then f t-f (t.erase e) else 0) p = 0 := by
    rw [← bernoulliPolynomial_zero (s.erase e) p]
    apply bernoulliPolynomial_congr
    intro t ht
    simp [show e ∉ t from fun hh => Finset.notMem_erase e s (ht hh)]
  rw [hclosed,mul_zero,zero_add]
  congr 1
  apply bernoulliPolynomial_congr
  intro t ht
  have het : e ∉ t := fun hh => Finset.notMem_erase e s (ht hh)
  simp [het]


end MarkedFirstMoment

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Moments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive marked moments and exponential estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedRecursion
attribute [local instance] Classical.propDecidable Classical.decEq


theorem conn_mem_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    {ω : Set E} (hω : ω ⊆ Q) {y : V} (hxy : Conn G ω x y) :
    y ∈ insert x (searchVertices G Q) := by
  induction hxy with
  | refl => exact Finset.mem_insert_self _ _
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact Finset.mem_insert_of_mem (mem_searchVertices G (hω he) (by simp [heq]))

end MarkedRecursion

section CutFactor
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

omit [Nonempty V] in
 
theorem bernoulliPolynomial_empty_indicator (F : Finset V) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m = ∅ then (1:ℝ) else 0) h = (1-h)^F.card := by
  unfold bernoulliPolynomial
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro m hm hne
    simp [hne]
  · simp


end CutFactor

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

omit [Nonempty V] in
theorem finiteRootComponent_subset (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (ω : Finset E) (hω : ω ⊆ Q) (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteRootComponent G ω x ⊆ F := by
  intro y hy
  have hxy : Conn G (ω : Set E) x y := by
    change y ∈ (finiteRootComponent G ω x : Set V) at hy
    rwa [coe_finiteRootComponent] at hy
  exact hF (conn_mem_searchSupport G Q x (by exact_mod_cast hω) hxy)

end PointwiseRecursion

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Goodness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section GoodnessGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteRootComponent_mono (G : BondGraph V E) {ω η : Finset E} (h : ω ⊆ η) (x : V) :
    finiteRootComponent G ω x ⊆ finiteRootComponent G η x := by
  intro y hy
  change y ∈ (finiteRootComponent G η x : Set V)
  rw [coe_finiteRootComponent]
  apply conn_mono G (show (ω : Set E) ⊆ η from h)
  change y ∈ (finiteRootComponent G ω x : Set V) at hy
  rwa [coe_finiteRootComponent] at hy


end GoodnessGeometry

section GoodnessLaw
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_finite_restriction (Q : Finset E) (A : Set (Set E)) :
    MeasurableSet {ω : Set E | ω ∩ (Q : Set E) ∈ A} := by
  have hm : MeasurableSet {η : Set (Q : Set E) | (Subtype.val '' η : Set E) ∈ A} := .of_discrete
  convert hm.preimage (measurable_set_restrict (Q : Set E)) using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  have he : (Subtype.val '' (Subtype.val ⁻¹' ω : Set (Q : Set E)) : Set E) = ω ∩ (Q : Set E) := by
    ext e
    simp [and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,he]

theorem incident_filter_card_le_degree (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (x : V) : (Q.filter fun e => x ∈ G e).card ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  have hex (e : {e // e ∈ Q.filter fun e => x ∈ G e}) : ∃ y, G e.val = s(x,y) :=
    Sym2.mem_iff_exists.mp (Finset.mem_filter.mp e.property).2
  let f : {e // e ∈ Q.filter fun e => x ∈ G e} → Step G x :=
    fun e => ⟨(e.val,(hex e).choose),(hex e).choose_spec⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : Step G x => z.val.1) hab)
  simpa only [degree,Nat.card_eq_fintype_card,Fintype.card_coe] using Fintype.card_le_of_injective f hf



end GoodnessLaw

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Spectral
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


theorem neighbors_card_le_degree (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    (neighbors G hloc x).card ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  let p : Step G x → {y // y ∈ neighbors G hloc x} :=
    fun d => ⟨d.val.2, (mem_neighbors G hloc x d.val.2).mpr ⟨d.val.1,d.property⟩⟩
  have hp : Function.Surjective p := by
    intro y
    obtain ⟨e,he⟩ := (mem_neighbors G hloc x y.val).mp y.property
    exact ⟨⟨(e,y.val),he⟩,Subtype.ext rfl⟩
  simpa only [degree,Nat.card_eq_fintype_card,Fintype.card_coe] using
    Fintype.card_le_of_surjective p hp

end IsoperimetricEnergy

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable

theorem operator_kernel_hasSum (A : Hilbert V →L[ℂ] Hilbert V) (f : Hilbert V) (x : V) :
    HasSum (fun y => matrixCoeff A x y * f y) (A f x) := by
  have h := ((lp.evalCLM ℂ (fun _ : V => ℂ) 2 x).comp A).hasSum
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) f)
  change HasSum (fun y => A (lp.single 2 y (f y)) x) (A f x) at h
  have heq : (fun y : V => A (lp.single 2 y (f y)) x) =
      (fun y => matrixCoeff A x y * f y) := by
    funext y
    have he : lp.single (E := fun _ : V => ℂ) 2 y (f y) =
        f y • lp.single 2 y (1:ℂ) := by
      rw [← lp.single_smul]; simp
    simp [he, matrixCoeff, mul_comm]
  rw [heq] at h
  exact h

@[simp] theorem matrixCoeff_mul (A B : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (A*B) x y = ∑' z, matrixCoeff A x z * matrixCoeff B z y := by
  exact (operator_kernel_hasSum A (B (lp.single 2 y (1:ℂ))) x).tsum_eq.symm

end InvariantOperatorTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_EndpointKernels
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section FiniteLocalIntegral
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteFieldWeight_eq_atom (Q : Finset E) (p : unitInterval) (ω : FiniteField Q) :
    finiteFieldWeight Q p ω = (law p : Measure (Set (Q : Set E))).real {finiteFieldEquiv Q ω} := by
  have hn : (finiteFieldEquiv Q ω).ncard = ω.val.card := by
    rw [finiteFieldEquiv_apply,Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
    · exact Set.ncard_coe_finset _
    · intro e he
      exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,rfl⟩
  rw [law,setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ,hn]
  have hc : Fintype.card (Q : Set E) = Q.card := Fintype.card_coe Q
  simp only [finiteFieldWeight,bernoulliWeight,Set.ncard_univ,Nat.card_eq_fintype_card,hc]

 

theorem integral_finite_local (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) :
    (∫ ω, f ω ∂law p) = ∑ η : FiniteField Q, finiteFieldWeight Q p η * f (finiteFieldSet Q η) := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have hmap := integral_map (μ := law p) (measurable_set_restrict (Q : Set E)).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable
  rw [law_map_restrict p (Q : Set E)] at hmap
  have he (ω : Set E) : g (Subtype.val ⁻¹' ω) = f ω := by
    rw [hf ω]
    dsimp [g]
    congr 1
    ext e
    simp [and_comm]
  simp_rw [he] at hmap
  rw [← hmap,integral_fintype Integrable.of_finite]
  rw [← (finiteFieldEquiv Q).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  rw [← finiteFieldWeight_eq_atom]
  simp only [g,finiteFieldEquiv_image,smul_eq_mul]

end FiniteLocalIntegral

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedGoodLocality
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_finite_local (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Integrable f (law p) := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  have hi : Integrable g (Measure.map (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) (law p)) := by
    rw [law_map_restrict]
    exact Integrable.of_finite
  rw [he]
  exact hi.comp_measurable (measurable_set_restrict (Q : Set E))

end CappedGoodLocality

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Amplification
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePathOperator
attribute [local instance] Classical.propDecidable Classical.decEq


namespace PositiveRealMatrix
variable {A H : Hilbert V →L[ℂ] Hilbert V}

theorem mul_hasSum (hA : PositiveRealMatrix A) (H : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    HasSum (fun z => (matrixCoeff A x z).re * (matrixCoeff H z y).re)
      (matrixCoeff (A*H) x y).re := by
  have h := Complex.reCLM.hasSum (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x)
  change HasSum (fun z => (matrixCoeff A x z * matrixCoeff H z y).re)
    (matrixCoeff (A*H) x y).re at h
  simpa only [Complex.mul_re,(hA _ _).1,zero_mul,sub_zero] using h

theorem mul (hA : PositiveRealMatrix A) (hH : PositiveRealMatrix H) :
    PositiveRealMatrix (A*H) := by
  intro x y
  constructor
  · have hs := (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x).summable
    change Summable (fun z => matrixCoeff A x z * matrixCoeff H z y) at hs
    rw [matrixCoeff_mul,Complex.im_tsum hs]
    simp only [Complex.mul_im,(hA _ _).1,(hH _ _).1,mul_zero,zero_mul,add_zero,tsum_zero]
  · rw [← (hA.mul_hasSum H x y).tsum_eq]
    exact tsum_nonneg fun z => mul_nonneg (hA x z).2 (hH z y).2

theorem one : PositiveRealMatrix (1 : Hilbert V →L[ℂ] Hilbert V) := by
  intro x y
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply]
  split_ifs <;> norm_num

theorem pow (hA : PositiveRealMatrix A) (k : ℕ) : PositiveRealMatrix (A^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (one (V := V))
  | succ k ih => rw [pow_succ]; exact ih.mul hA

end PositiveRealMatrix



end PositivePathOperator

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_Resampling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resampling for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicBall
attribute [local instance] Classical.propDecidable Classical.decEq


theorem intrinsicBall_mono (G : BondGraph V E) {ω η : Set E} (h : ω ⊆ η) (x : V) (M : ℕ) :
    intrinsicBall G ω x M ⊆ intrinsicBall G η x M := by
  rintro y ⟨l,hl,hlen,ho⟩
  exact ⟨l,hl,hlen,fun e he => h (ho e he)⟩

theorem Along.bonds_in_incidentBall {G : BondGraph V E} (hloc : LocallyFinite G)
    {x y : V} {l : List E} (h : Along G x l y) (M : ℕ) (hlen : l.length ≤ M) :
    ∀ e ∈ l, e ∈ incidentSupport G hloc (finite_reachBall hloc x M).toFinset := by
  rcases h.first_outside (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E)
    with h | ⟨a,b,e,l₁,l₂,heq,h₁,he,_,_,hnot⟩
  · exact h
  · exfalso
    apply hnot
    apply (mem_incidentSupport G hloc _ e).mpr
    refine ⟨a,?_,by simp [he]⟩
    apply (finite_reachBall hloc x M).mem_toFinset.mpr
    apply reachBall_mono G x (show l₁.length ≤ M by subst l; simp only [List.length_append,List.length_cons] at hlen; omega)
    exact h₁.mem_reachBall

theorem intrinsicBall_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E)) x M =
      intrinsicBall G ω x M := by
  apply Set.Subset.antisymm (intrinsicBall_mono G Set.inter_subset_left x M)
  rintro y ⟨l,hl,hlen,ho⟩
  exact ⟨l,hl,hlen,fun e he => ⟨ho e he,hl.bonds_in_incidentBall hloc M hlen e he⟩⟩

theorem integral_eq_bernoulliPolynomial (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q:Set E))) :
    (∫ ω, f ω ∂law p) = bernoulliPolynomial Q (fun η => f η) p := by
  rw [integral_finite_local Q p f hf]
  simp only [finiteFieldWeight,finiteFieldSet]
  rw [Finset.sum_coe_sort Q.powerset (fun η => bernoulliWeight Q η p * f η)]
  unfold bernoulliPolynomial
  apply Finset.sum_congr rfl
  intro η _
  unfold bernoulliWeight
  ring

end IntrinsicBall
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicMaximum
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicBondSupport_coe (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (M : ℕ) :
    (intrinsicBondSupport G hloc S x M : Set E) =
      (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) ∩ S := by
  ext e
  simp [intrinsicBondSupport]

theorem intrinsicBall_domain_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (S ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G (ω ∩ (intrinsicBondSupport G hloc S x M : Set E)) x M =
      intrinsicBall G (ω ∩ S) x M := by
  rw [intrinsicBondSupport_coe]
  have he : ω ∩ ((incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) ∩ S) =
      (ω ∩ S) ∩ (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) := by
    ext e; simp [and_left_comm,and_comm,and_assoc]
  rw [he,intrinsicBall_restrict G hloc]

end IntrinsicMaximum
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_KernelMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterMassMoments
attribute [local instance] Classical.propDecidable Classical.decEq


theorem measurable_clusterMass [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) : Measurable (fun ω => clusterMass G ω x) := by
  apply Measurable.tsum
  intro y
  exact Measurable.ite (measurableSet_conn G x y) measurable_const measurable_const

theorem lintegral_clusterMass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V) :
    (∫⁻ ω, clusterMass G ω x ∂law p) = ∑' y, law p {ω | Conn G ω x y} := by
  unfold clusterMass
  rw [lintegral_tsum (fun y => (Measurable.ite (measurableSet_conn G x y) measurable_const measurable_const).aemeasurable)]
  apply tsum_congr
  intro y
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using (lintegral_indicator_one (μ := law p) (measurableSet_conn G x y))

end ClusterMassMoments
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SusceptibilityTypes
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_twoPoint_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : Summable (twoPoint G p x) := by
  obtain ⟨_,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  exact summable_of_sum_le (twoPoint_nonneg G p x) (hrow x)

end SusceptibilityTypes
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_ExteriorMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped Topology
section ExteriorConnectionIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integral_event_indicator (p : unitInterval) (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ ω, (if ω ∈ A then (1:ℝ) else 0) ∂law p) = (law p).real A := by
  simpa only [Set.indicator,Pi.one_apply] using (integral_indicator_one (μ := law p) hA)



end ExteriorConnectionIndependence
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Susceptibility
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedSearchTransfer
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exponential_transfer_of_deriv_bound (H : ℝ → ℝ) (a b K : ℝ)
    (hH : Differentiable ℝ H) (hab : a ≤ b)
    (hb : ∀ t ∈ Set.Icc a b, deriv H t ≤ K*H t) :
    H b ≤ Real.exp (K*(b-a))*H a := by
  let F (t : ℝ) := Real.exp (-K*(t-a))*H t
  have hF (t : ℝ) : HasDerivAt F (Real.exp (-K*(t-a))*(deriv H t-K*H t)) t := by
    have he := (((hasDerivAt_id t).sub_const a).const_mul (-K)).exp
    convert! he.mul (hH t).hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    ring
  have hanti : AntitoneOn F (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hb t (interior_subset ht)))
  have h := hanti ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (K*(b-a))).le
  simpa only [F, sub_self,mul_zero,Real.exp_zero,one_mul,←mul_assoc,←Real.exp_add,
    neg_mul,add_neg_cancel,Real.exp_zero,one_mul,neg_zero,add_zero] using hm



end MarkedSearchTransfer
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedComponentIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem markedConnection_component_polynomial (G : BondGraph V E)
    (Q : Finset E) (x : V) (h p : ℝ) :
    markedConnectionPolynomial G Q x h p =
      bernoulliPolynomial Q (fun ω => 1-(1-h)^(finiteRootComponent G ω x).card) p := by
  apply bernoulliPolynomial_congr
  intro ω hω
  let C := finiteRootComponent G ω x
  let F := insert x (searchVertices G Q)
  have hCF : C ⊆ F := finiteRootComponent_subset G Q F x ω hω le_rfl
  have he (m : Finset V) : (∃ y ∈ m, Conn G (ω:Set E) x y) ↔ m ∩ C ≠ ∅ := by
    rw [Finset.nonempty_iff_ne_empty.symm]
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,Finset.mem_inter.mpr ⟨hy,by change y ∈ (C:Set V); simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hxy⟩⟩
    · rintro ⟨y,hy⟩
      refine ⟨y,(Finset.mem_inter.mp hy).1,?_⟩
      have hm : y ∈ (C:Set V) := (Finset.mem_inter.mp hy).2
      simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hm
  have hid : bernoulliPolynomial F (fun m => if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0) h =
      1-bernoulliPolynomial F (fun m => if m ∩ C = ∅ then 1 else 0) h := by
    calc
      _ = bernoulliPolynomial F (fun m => 1-(if m ∩ C = ∅ then 1 else 0)) h := by
        apply bernoulliPolynomial_congr
        intro m _
        by_cases hm : m ∩ C = ∅
        · have hn : ¬∃ y ∈ m, Conn G (ω:Set E) x y := fun hc => (he m).mp hc hm
          simp only [hm,hn,if_false,if_true,sub_self]
        · have hy := (he m).mpr hm
          simp only [hm,hy,if_false,if_true,sub_zero]
      _ = _ := by rw [bernoulliPolynomial_sub,bernoulliPolynomial_const]
  rw [hid,bernoulliPolynomial_restrict C F hCF (fun m => if m = ∅ then 1 else 0) h,
    bernoulliPolynomial_empty_indicator]

theorem one_sub_pow_one_sub_le (h : unitInterval) (n : ℕ) :
    1-(1-(h:ℝ))^n ≤ (h:ℝ)*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr h.2.2)
    have hn : 0 ≤ (h:ℝ)^2*n := by positivity
    nlinarith

end MarkedComponentIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedConnectionLaw
attribute [local instance] Classical.propDecidable Classical.decEq



theorem one_sub_pow_one_sub_ge_half (h : unitInterval) (n : ℕ)
    (hn : 1 ≤ (h:ℝ)*n) : (1:ℝ)/2 ≤ 1-(1-(h:ℝ))^n := by
  have hb (m : ℕ) : (1+(h:ℝ)*m)*(1-(h:ℝ))^m ≤ 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hp : 0 ≤ (1-(h:ℝ))^m := pow_nonneg (sub_nonneg.mpr h.2.2) _
      have ha : (1+(h:ℝ)*(m+1))*(1-(h:ℝ)) ≤ 1+(h:ℝ)*m := by
        have hh : 0 ≤ (h:ℝ)^2*((m:ℝ)+1) := by positivity
        nlinarith
      have hm := mul_le_mul_of_nonneg_right ha hp
      rw [Nat.cast_succ,pow_succ]
      nlinarith
  have hp : 0 ≤ (1-(h:ℝ))^n := pow_nonneg (sub_nonneg.mpr h.2.2) _
  have hm := mul_le_mul_of_nonneg_right hn hp
  have hb' := hb n
  nlinarith



end MarkedConnectionLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_FractionalMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterTailCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClusterTailIndicator_mono (G : BondGraph V E) (x : V) (n : ℕ) :
    Monotone (finiteClusterTailIndicator G x n) := by
  intro ω η hωη
  have hc := Finset.card_le_card (finiteRootComponent_mono G hωη x)
  unfold finiteClusterTailIndicator
  split_ifs <;> norm_num
  omega

end ClusterTailCovariance
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_TailBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteStretchedTail
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClusterTail_le_markedConnection (G : BondGraph V E) (Q : Finset E)
    (x : V) (n : ℕ) (p h : unitInterval) (hn : 1 ≤ (h:ℝ)*n) :
    finiteClusterTail G Q x n p ≤ 2*markedConnectionPolynomial G Q x h p := by
  have hh : (1:ℝ)/2*finiteClusterTail G Q x n p ≤ markedConnectionPolynomial G Q x h p := by
    rw [finiteClusterTail,←bernoulliPolynomial_const_mul,markedConnection_component_polynomial]
    apply bernoulliPolynomial_mono _ _ _ p p.2
    intro ω _
    unfold finiteClusterTailIndicator
    by_cases hs : n ≤ (finiteRootComponent G ω x).card
    · simp only [ite_eq_left hs,mul_one]
      apply one_sub_pow_one_sub_ge_half
      exact hn.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) h.2.1)
    · simp only [ite_eq_right hs,mul_zero]
      apply sub_nonneg.mpr
      exact pow_le_one₀ (sub_nonneg.mpr h.2.2) (by linarith [h.2.1])
  linarith



end FiniteStretchedTail
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section TailSummation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem natCast_eq_sum_tail (k M : ℕ) (hk : k ≤ M) :
    (k:ℝ) = ∑ i ∈ Finset.range M, if i+1 ≤ k then (1:ℝ) else 0 := by
  rw [Finset.sum_boole]
  congr 1
  have hh : (Finset.range M).filter (fun i => i+1 ≤ k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hh,Finset.card_range]

end TailSummation
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_ContactTrace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Trace for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section NonnegativeOperatorDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem ennMatrixCoeff_mul {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : PositiveRealMatrix A) (hB : PositiveRealMatrix B) (x y : V) :
    ennMatrixCoeff (A*B) x y = ∑' z, ennMatrixCoeff A x z * ennMatrixCoeff B z y := by
  unfold ennMatrixCoeff
  rw [←(hA.mul_hasSum B x y).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun z => mul_nonneg (hA x z).2 (hB z y).2) (hA.mul_hasSum B x y).summable]
  apply tsum_congr; intro z
  exact ENNReal.ofReal_mul (hA x z).2

theorem HasKernel.ennMatrixCoeff [Countable E] (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    ennMatrixCoeff T x y = law p {ω | Conn G ω x y} := by
  unfold Percolation.ennMatrixCoeff matrixCoeff
  rw [hT x y]
  simp only [Complex.ofReal_re,twoPoint,ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem HasKernel.positiveRealMatrix (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) : PositiveRealMatrix T := by
  intro x y
  change (T (lp.single 2 y (1:ℂ)) x).im = 0 ∧ 0 ≤ (T (lp.single 2 y (1:ℂ)) x).re
  rw [hT x y]
  exact ⟨rfl,twoPoint_nonneg G p x y⟩

end NonnegativeOperatorDiagram
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_TraceBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormRatio
attribute [local instance] Classical.propDecidable Classical.decEq



theorem HasKernel.norm_one_le [Countable E] [Nonempty V]
    (G : BondGraph V E) (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : 1 ≤ ‖T‖ := by
  let x : V := Classical.choice inferInstance
  have hd : twoPoint G p x x = 1 := twoPoint_self G p x
  have hh := (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (T (lp.single 2 x (1:ℂ))) x).trans (T.le_opNorm (lp.single 2 x (1:ℂ)))
  simpa [hT x x,hd,lp.norm_single] using hh

end NormRatio
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PublishedConsequences
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
namespace BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq

theorem law_restrict_finite_cluster (G : BondGraph V E) (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) (A : Set (Set E)) :
    law p {ω | ω ∈ A ∧ (cluster G ω x).Finite} = law p A := by
  apply measure_congr
  filter_upwards [hfin] with ω hω
  exact propext (and_iff_left hω)

theorem criticalFiniteTail_eq (G : BondGraph V E)
    (A : V → ℕ → Set (Set E)) (x : V)
    (hfin : ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite) :
    criticalFiniteTail G A x = criticalTail G A x := by
  funext n
  unfold criticalFiniteTail criticalTail
  rw [law_restrict_finite_cluster G (pc G) x hfin (A x n)]

end BenjaminiSchramm
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_EventMeasurability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem volumeEvent_eq_clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) :
    volumeEvent G x n = clusterLarge G x n := by
  ext ω
  constructor
  · intro h
    by_cases hf : (cluster G ω x).Finite
    · have hn : n ≤ (cluster G ω x).ncard := by
        change (n : ℕ∞) ≤ (cluster G ω x).encard at h
        rw [← hf.cast_ncard_eq] at h
        exact_mod_cast h
      exact ⟨hf.toFinset, by simpa only [← Set.ncard_eq_toFinset_card _ hf] using hn,
        fun y hy => hf.mem_toFinset.mp hy⟩
    · obtain ⟨t, ht, hn⟩ := (Set.not_finite.mp hf).exists_subset_card_eq n
      exact ⟨t, hn.ge, ht⟩
  · rintro ⟨t, hn, ht⟩
    change (n : ℕ∞) ≤ (cluster G ω x).encard
    have hsub : (t : Set V) ⊆ cluster G ω x := ht
    have hcard := Set.encard_le_encard hsub
    have hn' : (n : ℕ∞) ≤ (t.card : ℕ∞) := by exact_mod_cast hn
    exact hn'.trans (by simpa using hcard)

theorem measurableSet_volumeEvent [Countable E] (G : BondGraph V E) (x : V) (n : ℕ) :
    MeasurableSet (volumeEvent G x n) := by
  rw [volumeEvent_eq_clusterLarge]
  exact measurableSet_clusterLarge G x n

theorem along_exists_walk_length_le (G : BondGraph V E) (ω : Set E)
    {x y : V} {l : List E} (h : Along G x l y) (ho : ∀ e ∈ l, e ∈ ω) :
    ∃ w : (openSimpleGraph G ω).Walk x y, w.length ≤ l.length := by
  induction h with
  | nil => exact ⟨.nil, by simp⟩
  | @cons x z y l e he h ih =>
    obtain ⟨w, hw⟩ := ih (fun f hf => ho f (by simp [hf]))
    by_cases hxz : x = z
    · subst z
      exact ⟨w, hw.trans (by simp)⟩
    · refine ⟨.cons ⟨hxz, e, ho e (by simp), he⟩ w, ?_⟩
      change w.length + 1 ≤ l.length + 1
      exact Nat.add_le_add_right hw 1

theorem intrinsicBall_iff_distance_le (G : BondGraph V E) (ω : Set E)
    (x y : V) (M : ℕ) (hc : Conn G ω x y) :
    y ∈ intrinsicBall G ω x M ↔ (openSimpleGraph G ω).dist x y ≤ M := by
  constructor
  · rintro ⟨l, hl, hlen, ho⟩
    obtain ⟨w, hw⟩ := along_exists_walk_length_le G ω hl ho
    exact (SimpleGraph.dist_le w).trans (hw.trans hlen)
  · intro hd
    obtain ⟨w, hw⟩ := ((conn_iff_reachable G ω x y).mp hc).exists_walk_length_eq_dist
    obtain ⟨l, hl, he, ho⟩ := walk_lift_bonds G ω w
    have hlen : l.length = w.length := by
      have he' := congrArg List.length he
      simpa only [List.length_map, SimpleGraph.Walk.length_edges] using he'
    exact ⟨l, hl, hlen.trans_le (hw.trans_le hd), ho⟩

theorem measurableSet_mem_intrinsicBall (G : BondGraph V E) (hloc : LocallyFinite G)
    (x y : V) (M : ℕ) : MeasurableSet {ω | y ∈ intrinsicBall G ω x M} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : {ω | y ∈ intrinsicBall G ω x M} =
      {ω | ω ∩ (Q : Set E) ∈ {η | y ∈ intrinsicBall G η x M}} := by
    ext ω
    change (y ∈ intrinsicBall G ω x M) ↔ (y ∈ intrinsicBall G (ω ∩ (Q : Set E)) x M)
    rw [intrinsicBall_restrict G hloc]
  rw [he]
  exact measurableSet_finite_restriction Q _

theorem intrinsicRadiusEvent_eq (G : BondGraph V E) (x : V) {n : ℕ} (hn : 0 < n) :
    intrinsicRadiusEvent G x n =
      {ω | ∃ y, Conn G ω x y ∧ y ∉ intrinsicBall G ω x (n - 1)} := by
  ext ω
  constructor
  · rintro ⟨y, hy, hd⟩
    refine ⟨y, hy, ?_⟩
    rw [intrinsicBall_iff_distance_le G ω x y (n - 1) hy]
    omega
  · rintro ⟨y, hy, hd⟩
    refine ⟨y, hy, ?_⟩
    rw [intrinsicBall_iff_distance_le G ω x y (n - 1) hy] at hd
    omega

theorem measurableSet_intrinsicRadiusEvent [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (n : ℕ) :
    MeasurableSet (intrinsicRadiusEvent G x n) := by
  by_cases hn : n = 0
  · subst n
    have he : intrinsicRadiusEvent G x 0 = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact ⟨x, mem_cluster_self G ω x, Nat.zero_le _⟩
    rw [he]
    exact MeasurableSet.univ
  · rw [intrinsicRadiusEvent_eq G x (Nat.pos_of_ne_zero hn)]
    exact (Measurable.exists fun y =>
      (measurableSet_setOfPred.mp (measurableSet_conn G x y)).and
      (measurableSet_setOfPred.mp
        (measurableSet_mem_intrinsicBall G hloc x y (n - 1))).not).setOf

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Corridors
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section CorridorIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_inter_const (S : Set E) : Measurable (fun ω : Set E => ω ∩ S) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).and measurable_const


end CorridorIndependence
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Derivatives
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSizeBounds
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_ncard_le_pow (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (x : V) (k : ℕ) :
    (reachBall G x k).ncard ≤ (d+1)^k := by
  induction k with
  | zero => simp only [reachBall,Set.ncard_singleton,pow_zero,le_refl]
  | succ k ih =>
    let W := (finite_reachBall hloc x k).toFinset
    have he : reachBall G x (k+1) = (W ∪ W.biUnion (neighbors G hloc) : Finset V) := by
      ext z
      simp only [reachBall,Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,Finset.mem_coe,
        Finset.mem_union,Finset.mem_biUnion,mem_neighbors,Set.Finite.mem_toFinset,W,Adj,exists_prop]
    rw [he,Set.ncard_coe_finset]
    have hb : (W.biUnion (neighbors G hloc)).card ≤ W.card*d :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun a _ => (neighbors_card_le_degree G hloc a).trans (hd a))
    have hi : W.card ≤ (d+1)^k := by simpa only [W,←Set.ncard_eq_toFinset_card] using ih
    calc
      _ ≤ W.card + (W.biUnion (neighbors G hloc)).card := Finset.card_union_le _ _
      _ ≤ W.card + W.card*d := Nat.add_le_add_left hb _
      _ = W.card*(d+1) := by ring
      _ ≤ (d+1)^k*(d+1) := Nat.mul_le_mul_right _ hi
      _ = _ := (pow_succ _ _).symm

end CorridorSizeBounds
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostVolume
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

open MeasureTheory

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem markedConnection_le_truncated_tails (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (N : ℕ) :
    markedConnectionPolynomial G Q x h p ≤
      (h : ℝ) * (∑ i ∈ Finset.range N, finiteClusterTail G Q x (i + 1) p) +
        finiteClusterTail G Q x N p := by
  rw [markedConnection_component_polynomial]
  simp only [finiteClusterTail]
  rw [←bernoulliPolynomial_sum,←bernoulliPolynomial_const_mul,←bernoulliPolynomial_add]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  let m := (finiteRootComponent G ω x).card
  change 1 - (1 - (h : ℝ)) ^ m ≤
    (h : ℝ) * (∑ i ∈ Finset.range N, if i + 1 ≤ m then (1 : ℝ) else 0) +
      if N ≤ m then (1 : ℝ) else 0
  by_cases hm : m ≤ N
  · rw [←natCast_eq_sum_tail m N hm]
    exact (one_sub_pow_one_sub_le h m).trans
      (le_add_of_nonneg_right (by split_ifs <;> norm_num))
  · have hNm : N ≤ m := by omega
    rw [ite_eq_left hNm]
    have hs : 0 ≤ (h : ℝ) *
        (∑ i ∈ Finset.range N, if i + 1 ≤ m then (1 : ℝ) else 0) :=
      mul_nonneg h.2.1 (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    have hp := pow_nonneg (sub_nonneg.mpr h.2.2) m
    linarith

theorem inverse_sqrt_step (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℕ) ≤
      2 * (Real.sqrt (n + 1 : ℕ) - Real.sqrt n) := by
  have ha : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
  have hb := Real.sqrt_nonneg (n : ℝ)
  have hab : Real.sqrt (n : ℝ) ≤ Real.sqrt (n + 1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
  have ha2 := Real.sq_sqrt (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity)
  have hb2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
  apply (div_le_iff₀ ha).mpr
  have hdiff := sq_nonneg (Real.sqrt (n + 1 : ℕ) - Real.sqrt (n : ℝ))
  norm_num only [Nat.cast_add,Nat.cast_one] at ha2
  norm_num only [Nat.cast_add,Nat.cast_one] at ha hab hdiff ⊢
  nlinarith

theorem sum_inverse_sqrt_le (N : ℕ) :
    (∑ i ∈ Finset.range N, 1 / Real.sqrt (i + 1 : ℕ)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := inverse_sqrt_step N
    linarith

theorem finiteClusterTail_le_volume_probability [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    finiteClusterTail G Q x n p ≤ (law p (volumeEvent G x n)).toReal := by
  let f (ω : Set E) : ℝ := if n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard then 1 else 0
  have hf : ∀ ω, f ω = f (ω ∩ (Q : Set E)) := by
    intro ω
    simp only [f,Set.inter_assoc,Set.inter_self]
  have he : (∫ ω, f ω ∂law p) = finiteClusterTail G Q x n p := by
    rw [integral_eq_bernoulliPolynomial Q p f hf]
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [f,finiteClusterTailIndicator,
      Set.inter_eq_left.mpr (show (ω : Set E) ⊆ Q from hω),
      ←coe_finiteRootComponent,Set.ncard_coe_finset]
  rw [←he]
  change (∫ ω, f ω ∂law p) ≤ (law p).real (volumeEvent G x n)
  rw [←integral_event_indicator p (volumeEvent G x n)
    (measurableSet_volumeEvent G x n)]
  apply integral_mono (integrable_finite_local Q p f hf)
    (by simpa only [Set.indicator,Pi.one_apply] using!
      (integrable_const (1 : ℝ)).indicator (measurableSet_volumeEvent G x n))
  intro ω
  dsimp [f]
  split_ifs with hn hv
  · rfl
  · exfalso
    apply hv
    change (n : ℕ∞) ≤ (cluster G ω x).encard
    have hn' : (n : ℕ∞) ≤ ((cluster G (ω ∩ (Q : Set E)) x).ncard : ℕ∞) := by
      exact_mod_cast hn
    exact hn'.trans ((Set.ncard_le_encard _).trans
      (Set.encard_le_encard (fun y hy => conn_mono G Set.inter_subset_left hy)))
  · norm_num
  · rfl

theorem finiteClusterTail_le_criticalTail [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ)
    (p : unitInterval) (hp : p ≤ pc G) :
    finiteClusterTail G Q x n p ≤ criticalTail G (volumeEvent G) x n := by
  have hmono := bernoulliPolynomial_monotoneOn Q (finiteClusterTailIndicator G x n)
    (finiteClusterTailIndicator_mono G x n)
  exact (hmono p.2 (pc G).2 hp).trans
    (finiteClusterTail_le_volume_probability G Q x n (pc G))

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ExponentialDecay
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem mem_reachBall_of_graphDistance_le (G : BondGraph V E) (hconn : Connected G)
    (x z : V) (m : ℕ) (hd : graphDistance G x z ≤ m) : z ∈ reachBall G x m := by
  obtain ⟨w, hw⟩ := ((conn_iff_reachable G Set.univ x z).mp
    (conn_univ_of_connected G hconn x z)).exists_walk_length_eq_dist
  obtain ⟨l, hl, he, _⟩ := walk_lift_bonds G Set.univ w
  have hlen : l.length = w.length := by
    have hh := congrArg List.length he
    simpa only [List.length_map, SimpleGraph.Walk.length_edges] using hh
  exact reachBall_mono G x (hlen.trans_le (hw.trans_le hd)) hl.mem_reachBall

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Divergence
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
open scoped Classical
open Real

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [Fintype X]

lemma mul_log_div_ge_sub {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hs : 0 < p → 0 < r) : p - r ≤ p * Real.log (p / r) := by
  rcases eq_or_lt_of_le hp with rfl | hp
  · simp only [zero_sub, zero_mul]
    exact neg_nonpos.mpr hr
  · have hr := hs hp
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hr hp)) hp.le
    rw [Real.log_div hr.ne' hp.ne'] at h
    rw [Real.log_div hp.ne' hr.ne']
    have he : p * (r / p - 1) = r - p := by field_simp
    rw [he] at h
    nlinarith

lemma mass_sub_le_divergence (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x) - (∑ x, R x) ≤ divergence P R := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun x _ => mul_log_div_ge_sub (hP x) (hR x) (hs x)

lemma divergence_nonneg (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1) (hRsum : ∑ x, R x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) : 0 ≤ divergence P R := by
  simpa only [hPsum, hRsum, sub_self] using mass_sub_le_divergence P R hP hR hs

lemma normalizer_pos (P R : X → ℝ) (_hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) (g : X → ℝ) :
    0 < ∑ x, R x * Real.exp (g x) := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < P x := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun x _ => h x)
    linarith
  exact (mul_pos (hs x hx) (Real.exp_pos _)).trans_le
    (Finset.single_le_sum (fun y _ => mul_nonneg (hR y) (Real.exp_nonneg _)) (Finset.mem_univ x))

theorem entropy_inequality (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) (g : X → ℝ) :
    ∑ x, P x * g x ≤ divergence P R + Real.log (∑ x, R x * Real.exp (g x)) := by
  let Z := ∑ x, R x * Real.exp (g x)
  have hZ : 0 < Z := normalizer_pos P R hP hR hPsum hs g
  let R' := fun x => R x * Real.exp (g x) / Z
  have hR' : ∀ x, 0 ≤ R' x := fun x => div_nonneg
    (mul_nonneg (hR x) (Real.exp_nonneg _)) hZ.le
  have hs' : ∀ x, 0 < P x → 0 < R' x := fun x hx => div_pos
    (mul_pos (hs x hx) (Real.exp_pos _)) hZ
  have hRsum : ∑ x, R' x = 1 := by
    simp only [R', ← Finset.sum_div, Z, div_self hZ.ne']
  have hdiv := divergence_nonneg P R' hP hR' hPsum hRsum hs'
  have he : divergence P R' = divergence P R - (∑ x, P x * g x) + Real.log Z := by
    have hterm (x : X) : P x * Real.log (P x / R' x) =
        P x * Real.log (P x / R x) - P x * g x + P x * Real.log Z := by
      rcases eq_or_lt_of_le (hP x) with hx | hx
      · simp [← hx]
      · have hr := hs x hx
        simp only [R', Real.log_div hx.ne' (ne_of_gt (hs' x hx)),
          Real.log_div (mul_pos hr (Real.exp_pos _)).ne' hZ.ne',
          Real.log_mul hr.ne' (Real.exp_ne_zero _), Real.log_exp,
          Real.log_div hx.ne' hr.ne']
        ring
    simp only [divergence, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hPsum, one_mul]
  rw [he] at hdiv
  linarith

end CriticalPercolation.FiniteEntropy

open Set Real
open scoped Topology

namespace CriticalPercolation.FiniteEntropy

lemma mul_log_div_le {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) :
    r * Real.log (r/p) ≤ r * (r/p - 1) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp
  · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hr hp)) hr.le

theorem binaryDivergence_upper {p r : ℝ} (hp : p ∈ Ioo 0 1) (hr : r ∈ Icc 0 1) :
    binaryDivergence r p ≤ (r-p)^2 / (p*(1-p)) := by
  have hq : 0 < 1-p := sub_pos.mpr hp.2
  have h1 := mul_log_div_le hr.1 hp.1
  have h2 := mul_log_div_le (sub_nonneg.mpr hr.2) hq
  have he : r * (r/p-1) + (1-r)*((1-r)/(1-p)-1) = (r-p)^2/(p*(1-p)) := by
    field_simp [hp.1.ne', hq.ne']
    ring
  exact (add_le_add h1 h2).trans_eq he

lemma mul_log_div_eq {r p : ℝ} (hp : p ≠ 0) :
    r * Real.log (r / p) = r * Real.log r - r * Real.log p := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [Real.log_div hr hp]
    ring

lemma continuous_binaryRemainder (p : ℝ) : Continuous (binaryRemainder p) := by
  unfold binaryRemainder
  fun_prop

lemma binaryRemainder_eq {p : ℝ} (hp : p ∈ Ioo 0 1) (r : ℝ) :
    binaryRemainder p r = binaryDivergence r p - 2*(r-p)^2 := by
  unfold binaryRemainder binaryDivergence
  rw [mul_log_div_eq hp.1.ne', mul_log_div_eq (sub_pos.mpr hp.2).ne']
  ring

lemma hasDerivAt_binaryRemainder (p : ℝ) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasDerivAt (binaryRemainder p)
      (Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p)) r := by
  have hid := hasDerivAt_id r
  have ho := (hasDerivAt_const r (1:ℝ)).sub hid
  have hmul := (Real.hasDerivAt_mul_log hr.1.ne').add
    ((Real.hasDerivAt_mul_log (sub_pos.mpr hr.2).ne').comp r ho)
  convert ((hmul.sub (hid.mul_const (Real.log p))).sub
    (ho.mul_const (Real.log (1-p)))).sub
      (((hid.sub_const p).pow 2).const_mul 2) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

lemma hasDerivAt_binaryRemainder_deriv (p : ℝ) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasDerivAt
      (fun r => Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p))
      (r⁻¹ + (1-r)⁻¹ - 4) r := by
  have hid := hasDerivAt_id r
  have ho := (hasDerivAt_const r (1:ℝ)).sub hid
  convert (((((Real.hasDerivAt_log hr.1.ne').sub
    ((Real.hasDerivAt_log (sub_pos.mpr hr.2).ne').comp r ho)).sub_const
      (Real.log p)).add_const (Real.log (1-p))).sub
        ((hid.sub_const p).const_mul 4)) using 1 <;> first | rfl | ring

lemma binary_second_deriv_nonneg {r : ℝ} (hr : r ∈ Ioo 0 1) :
    0 ≤ r⁻¹ + (1-r)⁻¹ - 4 := by
  have hq : 0 < 1-r := sub_pos.mpr hr.2
  have he : r⁻¹ + (1-r)⁻¹ - 4 = (2*r-1)^2 / (r*(1-r)) := by
    field_simp [hr.1.ne', hq.ne']
    ring
  rw [he]
  exact div_nonneg (sq_nonneg _) (mul_pos hr.1 hq).le

lemma convexOn_binaryRemainder (p : ℝ) : ConvexOn ℝ (Icc 0 1) (binaryRemainder p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0:ℝ) 1)
    (continuous_binaryRemainder p).continuousOn
    (f' := fun r => Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p))
    (f'' := fun r => r⁻¹ + (1-r)⁻¹ - 4)
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_binaryRemainder p hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_binaryRemainder_deriv p hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact binary_second_deriv_nonneg hr

theorem binaryDivergence_lower {p r : ℝ} (hp : p ∈ Ioo 0 1) (hr : r ∈ Icc 0 1) :
    2*(r-p)^2 ≤ binaryDivergence r p := by
  have hconv := convexOn_binaryRemainder p
  have hder : HasDerivAt (binaryRemainder p) 0 p := by
    simpa using hasDerivAt_binaryRemainder p hp
  have hmin : binaryRemainder p p ≤ binaryRemainder p r := by
    rcases lt_trichotomy p r with h | rfl | h
    · have hs := hconv.le_slope_of_hasDerivAt ⟨hp.1.le, hp.2.le⟩ hr h hder
      rw [slope_def_field] at hs
      have ht := (le_div_iff₀ (sub_pos.mpr h)).mp hs
      simpa using ht
    · rfl
    · have hs := hconv.slope_le_of_hasDerivAt hr ⟨hp.1.le, hp.2.le⟩ h hder
      rw [slope_def_field] at hs
      have ht := (div_le_iff₀ (sub_pos.mpr h)).mp hs
      linarith
  rw [binaryRemainder_eq hp, binaryRemainder_eq hp] at hmin
  have hz : binaryDivergence p p = 0 := by
    simp [binaryDivergence, hp.1.ne', (sub_pos.mpr hp.2).ne']
  rw [hz] at hmin
  nlinarith

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CriticalSusceptibility
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem volume_threshold_le_clusterMass (G : BondGraph V E) (ω : Set E)
    (x : V) (n : ℕ) (hn : ω ∈ volumeEvent G x n) :
    (n : ℝ≥0∞) ≤ clusterMass G ω x := by
  rw [volumeEvent_eq_clusterLarge] at hn
  obtain ⟨F,hF,hsub⟩ := hn
  have he : (∑ y ∈ F, if Conn G ω x y then (1 : ℝ≥0∞) else 0) = F.card := by
    calc
      _ = ∑ _y ∈ F, (1 : ℝ≥0∞) :=
        Finset.sum_congr rfl (fun y hy => ite_eq_left (hsub y hy))
      _ = _ := by simp
  calc
    (n : ℝ≥0∞) ≤ F.card := by exact_mod_cast hF
    _ = ∑ y ∈ F, if Conn G ω x y then (1 : ℝ≥0∞) else 0 := he.symm
    _ ≤ clusterMass G ω x := ENNReal.sum_le_tsum F

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ProbabilityLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_finite_ae_of_finite_mass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V)
    (hf : (∑' y, law p {ω | Conn G ω x y}) ≠ ⊤) :
    ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
  have hi : (∫⁻ ω, clusterMass G ω x ∂law p) ≠ ⊤ := by
    rwa [lintegral_clusterMass]
  filter_upwards [ae_lt_top (measurable_clusterMass G x) hi] with ω hω
  by_contra hinf
  have hinf : (cluster G ω x).Infinite := hinf
  obtain ⟨n,hn⟩ := exists_nat_gt (clusterMass G ω x).toReal
  have hvol : ω ∈ volumeEvent G x n := by
    change (n : ℕ∞) ≤ (cluster G ω x).encard
    rw [Set.encard_eq_top hinf]
    exact le_top
  have hb := ENNReal.toReal_mono hω.ne (volume_threshold_le_clusterMass G ω x n hvol)
  rw [ENNReal.toReal_natCast] at hb
  exact (not_lt_of_ge hb) hn

theorem uniform_testSets_of_good_cost [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval)
    (hgood : ∀ x, ∃ S : Finset V, x ∈ S ∧ boundaryCost G hloc S x (p : ℝ) < 1) :
    ∃ (L : ℕ) (a : ℝ), a < 1 ∧ ∀ x, ∃ S : Finset V,
      x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p : ℝ) ≤ a := by
  obtain ⟨O,hO⟩ := hqt
  choose S hmem hcost using hgood
  have hOn : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO (Classical.ofNonempty : V)
    exact ⟨o,ho⟩
  let L := O.sup (fun x => (S x).card)
  let a := O.sup' hOn (fun x => boundaryCost G hloc (S x) x (p : ℝ))
  refine ⟨L,a,(Finset.sup'_lt_iff hOn).mpr (fun x _ => hcost x),?_⟩
  intro x
  obtain ⟨o,ho,α,β,hαβ,rfl⟩ := hO x
  refine ⟨(S o).map α.toEmbedding,?_,?_,?_⟩
  · simp only [Finset.mem_map,Equiv.toEmbedding_apply]
    exact ⟨o,hmem o,rfl⟩
  · simpa only [Finset.card_map] using Finset.le_sup (f := fun x => (S x).card) ho
  · rw [boundaryCost_aut G hloc hαβ]
    exact Finset.le_sup' (f := fun x => boundaryCost G hloc (S x) x (p : ℝ)) ho

theorem finite_mass_of_uniform_testSets [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (L : ℕ) (a : ℝ) (ha : a < 1)
    (htest : ∀ x, ∃ S : Finset V,
      x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p : ℝ) ≤ a) (x : V) :
    (∑' y, law p {ω | Conn G ω x y}) ≠ ⊤ := by
  let : Encodable V := Encodable.ofCountable V
  have hrow (F : Finset V) : ∑ y ∈ F, twoPoint G p x y ≤ (L : ℝ) / (1 - a) := by
    apply le_of_tendsto (tendsto_finsetSum F (fun y _ => tendsto_domainTwoPoint G p x y))
    obtain ⟨N,hN⟩ := subset_vertexExhaustion F
    filter_upwards [eventually_ge_atTop N] with n hn
    have hFn : F ⊆ vertexExhaustion n := hN.trans (vertexExhaustion_mono hn)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hFn (fun _ _ _ => measureReal_nonneg)).trans
      (domainRow_uniform_bound G hloc p L a ha htest (vertexExhaustion n) x)
  have hs := summable_of_sum_le (twoPoint_nonneg G p x) hrow
  have he : ENNReal.ofReal (susceptibility G p x) =
      ∑' y, law p {ω | Conn G ω x y} := by
    rw [susceptibility,ENNReal.ofReal_tsum_of_nonneg (twoPoint_nonneg G p x) hs]
    apply tsum_congr
    intro y
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [←he]
  exact ENNReal.ofReal_ne_top

theorem exists_bad_cost_of_pc_lt [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : pc G < p) :
    ∃ x, ∀ S : Finset V, x ∈ S → 1 ≤ boundaryCost G hloc S x (p : ℝ) := by
  by_contra! hgood
  obtain ⟨L,a,ha,htest⟩ := uniform_testSets_of_good_cost G hloc hqt p hgood
  have hfin (x : V) : ∀ᵐ ω ∂law p, (cluster G ω x).Finite :=
    cluster_finite_ae_of_finite_mass G p x
      (finite_mass_of_uniform_testSets G hloc p L a ha htest x)
  have hz : law p {ω | (infiniteClusters G ω).Nonempty} = 0 := by
    have he : {ω | (infiniteClusters G ω).Nonempty} =
        ⋃ x, {ω | (cluster G ω x).Infinite} := by
      ext ω
      simp only [infiniteClusters_nonempty_iff,Set.mem_iUnion,Set.mem_ofPred_eq]
    rw [he]
    exact measure_iUnion_null (fun x => ae_iff.mp (hfin x))
  obtain ⟨q,hq,hqp⟩ := sInf_lt_iff.mp hp
  have hpos : 0 < law p {ω | (infiniteClusters G ω).Nonempty} :=
    hq.trans_le (exists_infinite_cluster_probability_mono G hqp.le)
  rw [hz] at hpos
  exact hpos.false

theorem percolationProbability_mul_twoPoint_le [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    percolationProbability G p x * twoPoint G p x y ≤ percolationProbability G p y := by
  apply (association_infinite_conn G p x x y).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro ω ⟨hi,hc⟩
  change (cluster G ω y).Infinite
  rwa [←cluster_eq_of_conn G ω hc]

theorem percolationProbability_lower_of_bad_cost [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (r p : unitInterval)
    (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S : Finset V, x ∈ S → 1 ≤ boundaryCost G hloc S x (r : ℝ)) :
    1 - Real.exp ((r : ℝ) - p) ≤ percolationProbability G p x := by
  apply infinite_cluster_probability_ge_of_escape G hloc x p
  intro Λ
  rw [←finite_escape_eq_law G hloc Λ x p]
  apply (finite_escape_probability_lower G Λ x (incidentSupport G hloc Λ)
    r p hr hrp hp ?_).2
  intro S hS hx
  rw [boundaryExpectation_eq_of_incident_subset G hloc S x _
    (incidentSupport_mono G hloc hS)]
  exact hcost S hx

theorem one_sub_exp_neg_linear (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (-1) * s ≤ 1 - Real.exp (-s) := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp s) (Real.exp_pos (-s)).le
  rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  have he : Real.exp (-1) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have hl := mul_le_mul_of_nonneg_right he hs0
  nlinarith

theorem percolationProbability_linear_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (x : V) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : unitInterval, pc G < p → p < 1 →
      c * ((p : ℝ) - pc G) ≤ percolationProbability G p x := by
  obtain ⟨O,hO⟩ := hqt
  have hqt : QuasiTransitive G := ⟨O,hO⟩
  have hOn : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO x
    exact ⟨o,ho⟩
  have hpc0 : 0 < pc G := pc_pos G hloc hqt
  let a : ℝ := O.inf' hOn (fun o => twoPoint G (pc G) o x)
  have ha : 0 < a := (Finset.lt_inf'_iff hOn).mpr
    (fun o _ => twoPoint_pos G hconn (pc G) hpc0 o x)
  refine ⟨a * Real.exp (-1) / 2,by positivity,fun p hp hp1 => ?_⟩
  have hpR : (pc G : ℝ) < (p : ℝ) := hp
  let r : unitInterval := ⟨((p : ℝ) + pc G) / 2,
    ⟨by linarith [p.2.1,(pc G).2.1],by linarith [p.2.2,(pc G).2.2]⟩⟩
  have hrc : pc G < r := by change (pc G : ℝ) < ((p : ℝ) + pc G) / 2; linarith only [hpR]
  have hrp : r < p := by change ((p : ℝ) + pc G) / 2 < (p : ℝ); linarith only [hpR]
  obtain ⟨z,hcost⟩ := exists_bad_cost_of_pc_lt G hloc hqt r hrc
  have hb := percolationProbability_lower_of_bad_cost G hloc z r p (hpc0.trans hrc) hrp hp1 hcost
  obtain ⟨o,ho,α,β,hαβ,rfl⟩ := hO z
  have hθ : 1 - Real.exp ((r : ℝ) - p) ≤ percolationProbability G p o := by
    change 1 - Real.exp ((r : ℝ) - p) ≤ (law p).real {ω | (cluster G ω (α o)).Infinite} at hb
    rw [infinite_cluster_aut G p hαβ] at hb
    exact hb
  have hτ : a ≤ twoPoint G p o x :=
    (Finset.inf'_le (f := fun o => twoPoint G (pc G) o x) ho).trans
      (twoPoint_mono G o x hp.le)
  have ht := (mul_le_mul_of_nonneg_left hτ
    (show 0 ≤ percolationProbability G p o from ENNReal.toReal_nonneg)).trans
      (percolationProbability_mul_twoPoint_le G p o x)
  let s : ℝ := (p : ℝ) - r
  have hs0 : 0 ≤ s := sub_nonneg.mpr hrp.le
  have hs1 : s ≤ 1 := by dsimp [s]; linarith [p.2.2,r.2.1]
  have hl := one_sub_exp_neg_linear s hs0 hs1
  have he : (r : ℝ) - p = -s := by dsimp [s]; ring
  rw [he] at hθ
  have hm := mul_le_mul_of_nonneg_right (hl.trans hθ) ha.le
  have hid : (Real.exp (-1) * s) * a =
      (a * Real.exp (-1) / 2) * ((p : ℝ) - pc G) := by dsimp [s,r]; ring
  rw [hid] at hm
  exact hm.trans ht

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_EntropyEvent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

open CriticalPercolation.FiniteEntropy

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (1 : ℝ))
    (Real.exp_pos (-1)).le
  have he : Real.exp (1 : ℝ) * Real.exp (-1) = 1 := by rw [←Real.exp_add]; norm_num
  rw [he] at hh
  norm_num only [one_add_one_eq_two] at hh
  linarith

theorem event_mass_le_two_add_divergence
    {X : Type*} [Fintype X] (P Q : X → ℝ) (A : X → Bool)
    (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hPsum : ∑ x, P x = 1) (hQsum : ∑ x, Q x = 1)
    (hs : ∀ x, 0 < P x → 0 < Q x) :
    (∑ x, if A x then Q x else 0) ≤
      2 * (∑ x, if A x then P x else 0) + 2 * divergence P Q := by
  let g : X → ℝ := fun x => if A x then -1 else 0
  let a : ℝ := ∑ x, if A x then P x else 0
  let b : ℝ := ∑ x, if A x then Q x else 0
  have hb : 0 ≤ b := Finset.sum_nonneg (fun x _ => by split_ifs; exact hQ x; rfl)
  have htest : (∑ x, P x * g x) = -a := by
    dsimp only [a]
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [g]
    split_ifs <;> ring
  have hZ : (∑ x, Q x * Real.exp (g x)) = 1 - (1 - Real.exp (-1)) * b := by
    dsimp only [b]
    calc
      _ = (∑ x, Q x) - (1 - Real.exp (-1)) * (∑ x, if A x then Q x else 0) := by
        rw [Finset.mul_sum,←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        dsimp [g]
        split_ifs
        · ring
        · rw [Real.exp_zero]
          ring
      _ = _ := by rw [hQsum]
  have hZpos := normalizer_pos P Q hP hQ hPsum hs g
  have hlog := Real.log_le_sub_one_of_pos hZpos
  have hentropy := entropy_inequality P Q hP hQ hPsum hs g
  rw [htest,hZ] at hentropy
  rw [hZ] at hlog
  have hh := mul_le_mul_of_nonneg_right exp_neg_one_le_half hb
  change b ≤ 2 * a + 2 * divergence P Q
  linarith

theorem divergence_mul
    {X : Type*} [Fintype X] (P Q : X → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 < Q x) (hPsum : ∑ x, P x = 1)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    divergence (fun x => a * P x) (fun x => b * Q x) =
      a * divergence P Q + a * Real.log (a / b) := by
  have ht (x : X) : (a * P x) * Real.log ((a * P x) / (b * Q x)) =
      a * (P x * Real.log (P x / Q x)) + (a * Real.log (a / b)) * P x := by
    rw [show (a * P x) / (b * Q x) = (a / b) * (P x / Q x) by ring,
      Real.log_mul (div_ne_zero ha.ne' hb.ne') (div_ne_zero (hP x).ne' (hQ x).ne')]
    ring
  simp only [divergence,ht,Finset.sum_add_distrib,←Finset.mul_sum,hPsum,mul_one]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ProbeEntropy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

open CriticalPercolation.FiniteEntropy

namespace ProbeEntropy

open ProbeTree

theorem weight_pos (p h : ℝ) (hp : p ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1)
    (t : ProbeTree) (l : t.Leaf) : 0 < weight p h t l := by
  induction t with
  | done b => exact zero_lt_one
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_pos (sub_pos.mpr hp.2) (ih₀ l)
    | inr l => exact mul_pos hp.1 (ih₁ l)
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_pos (sub_pos.mpr hh.2) (ih₀ l)
    | inr l => exact mul_pos hh.1 (ih₁ l)

theorem totalQueries_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    totalQueries p h (.edge t₀ t₁) =
      1 + (1-p) * totalQueries p h t₀ + p * totalQueries p h t₁ := by
  simp only [totalQueries,Fintype.sum_sum_type,weight,queries,Nat.cast_add,Nat.cast_one]
  simp_rw [mul_add,mul_one,mul_assoc]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,sum_weight,mul_one]
  ring

theorem totalQueries_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    totalQueries p h (.mark t₀ t₁) =
      (1-h) * totalQueries p h t₀ + h * totalQueries p h t₁ := by
  simp only [totalQueries,Fintype.sum_sum_type,weight,queries,mul_assoc,←Finset.mul_sum]

theorem totalMarks_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    totalMarks p h (.edge t₀ t₁) =
      (1-p) * totalMarks p h t₀ + p * totalMarks p h t₁ := by
  simp only [totalMarks,Fintype.sum_sum_type,weight,marks,mul_assoc,←Finset.mul_sum]

theorem totalMarks_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    totalMarks p h (.mark t₀ t₁) =
      1 + (1-h) * totalMarks p h t₀ + h * totalMarks p h t₁ := by
  simp only [totalMarks,Fintype.sum_sum_type,weight,marks,Nat.cast_add,Nat.cast_one]
  simp_rw [mul_add,mul_one,mul_assoc]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,sum_weight,mul_one]
  ring

theorem treeDivergence_edge (p q h : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (hq : q ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1) (t₀ t₁ : ProbeTree) :
    treeDivergence p q h (.edge t₀ t₁) = binaryDivergence p q +
      (1-p) * treeDivergence p q h t₀ + p * treeDivergence p q h t₁ := by
  have he : treeDivergence p q h (.edge t₀ t₁) =
      divergence (fun l => (1-p) * weight p h t₀ l) (fun l => (1-q) * weight q h t₀ l) +
      divergence (fun l => p * weight p h t₁ l) (fun l => q * weight q h t₁ l) := by
    simp only [treeDivergence,divergence,Fintype.sum_sum_type,weight]
  rw [he,divergence_mul _ _ (weight_pos p h hp hh t₀) (weight_pos q h hq hh t₀)
    (sum_weight p h t₀) _ _ (sub_pos.mpr hp.2) (sub_pos.mpr hq.2),
    divergence_mul _ _ (weight_pos p h hp hh t₁) (weight_pos q h hq hh t₁)
    (sum_weight p h t₁) _ _ hp.1 hq.1]
  dsimp [treeDivergence,binaryDivergence]
  ring

theorem treeDivergence_mark (p q h : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (hq : q ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1) (t₀ t₁ : ProbeTree) :
    treeDivergence p q h (.mark t₀ t₁) =
      (1-h) * treeDivergence p q h t₀ + h * treeDivergence p q h t₁ := by
  have he : treeDivergence p q h (.mark t₀ t₁) =
      divergence (fun l => (1-h) * weight p h t₀ l) (fun l => (1-h) * weight q h t₀ l) +
      divergence (fun l => h * weight p h t₁ l) (fun l => h * weight q h t₁ l) := by
    simp only [treeDivergence,divergence,Fintype.sum_sum_type,weight]
  rw [he,divergence_mul _ _ (weight_pos p h hp hh t₀) (weight_pos q h hq hh t₀)
    (sum_weight p h t₀) _ _ (sub_pos.mpr hh.2) (sub_pos.mpr hh.2),
    divergence_mul _ _ (weight_pos p h hp hh t₁) (weight_pos q h hq hh t₁)
    (sum_weight p h t₁) _ _ hh.1 hh.1]
  simp only [div_self (sub_pos.mpr hh.2).ne',div_self hh.1.ne',Real.log_one,mul_zero,add_zero,
    treeDivergence]

theorem treeDivergence_eq (p q h : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (hq : q ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1) (t : ProbeTree) :
    treeDivergence p q h t = binaryDivergence p q * totalQueries p h t := by
  induction t with
  | done b => simp [treeDivergence,divergence,weight]
  | edge t₀ t₁ ih₀ ih₁ =>
    rw [treeDivergence_edge p q h hp hq hh,totalQueries_edge,ih₀,ih₁]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    rw [treeDivergence_mark p q h hp hq hh,totalQueries_mark,ih₀,ih₁]
    ring

theorem successMass_transfer (p q h : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (hq : q ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1) (t : ProbeTree) :
    successMass q h t ≤ 2 * successMass p h t +
      2 * binaryDivergence p q * totalQueries p h t := by
  have hb := event_mass_le_two_add_divergence (weight p h t) (weight q h t)
    (outcome t) (fun l => (weight_pos p h hp hh t l).le)
    (fun l => (weight_pos q h hq hh t l).le) (sum_weight p h t) (sum_weight q h t)
    (fun l _ => weight_pos q h hq hh t l)
  change successMass q h t ≤ 2 * successMass p h t + 2 * treeDivergence p q h t at hb
  rw [treeDivergence_eq p q h hp hq hh] at hb
  simpa only [mul_assoc] using hb

theorem totalMarks_eq_successMass (p h : ℝ) {t : ProbeTree} (ht : IsMarkSearch t) :
    h * totalMarks p h t = successMass p h t := by
  induction ht with
  | fail => simp
  | @edge t₀ t₁ _ _ ih₀ ih₁ =>
    rw [totalMarks_edge,successMass_edge]
    rw [←ih₀,←ih₁]
    ring
  | @mark t₀ _ ih =>
    rw [totalMarks_mark,successMass_mark]
    simp only [totalMarks_done,successMass_done,if_true,mul_zero,add_zero,mul_one]
    rw [←ih]
    ring

theorem totalQueries_le (p h : unitInterval) {t : ProbeTree} (ht : IsMarkSearch t)
    (d : ℕ) (hcost : ∀ l, queries t l ≤ d * marks t l) (hh : 0 < (h : ℝ)) :
    totalQueries p h t ≤ (d : ℝ) * successMass p h t / h := by
  apply (le_div_iff₀ hh).mpr
  have hb : totalQueries p h t ≤ (d : ℝ) * totalMarks p h t := by
    simp only [totalQueries,totalMarks,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    have hh := mul_le_mul_of_nonneg_left
      (show (queries t l : ℝ) ≤ (d : ℝ) * marks t l by exact_mod_cast hcost l)
      (weight_nonneg p h t l)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hb hh.le
  rw [mul_assoc,mul_comm (totalMarks p h t) (h : ℝ),
    totalMarks_eq_successMass p h ht] at hm
  exact hm

end ProbeEntropy
end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem markedConnection_entropy_comparison
    (G : BondGraph V E) (Q : Finset E) (x : V) (p q h : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) (hq : (q : ℝ) ∈ Set.Ioo 0 1)
    (hh : (h : ℝ) ∈ Set.Ioo 0 1) (d : ℕ)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    markedConnectionPolynomial G Q x h q ≤
      (2 + 2 * (d : ℝ) * ((p : ℝ) - q) ^ 2 / ((q : ℝ) * (1-q) * h)) *
        markedConnectionPolynomial G Q x h p := by
  let t := (markedClusterTree G Q x).forget
  have ht : ProbeTree.IsMarkSearch t := .mark (clusterSearch_markSearch G _ _ _)
  have hcost : ∀ l, ProbeTree.queries t l ≤ d * ProbeTree.marks t l := by
    simpa only [ProbeTree.Budget,zero_add] using markedClusterTree_budget G Q x d hdeg
  have hb := ProbeEntropy.successMass_transfer p q h hp hq hh t
  have hc := ProbeEntropy.totalQueries_le p h ht d hcost hh.1
  have hk := CriticalPercolation.FiniteEntropy.binaryDivergence_upper hq p.2
  have hkn : 0 ≤ CriticalPercolation.FiniteEntropy.binaryDivergence p q := by
    have hl := CriticalPercolation.FiniteEntropy.binaryDivergence_lower hq p.2
    nlinarith [sq_nonneg ((p : ℝ) - q)]
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hkn)
  have hn : 0 ≤ (d : ℝ) * ProbeTree.successMass p h t / h := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (ProbeTree.successMass_nonneg p h t)) hh.1.le
  have hk' := mul_le_mul_of_nonneg_right hk hn
  have hbound := hb.trans (add_le_add_right (hm.trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hk' (by norm_num : (0 : ℝ) ≤ 2))) _)
  rw [markedConnectionPolynomial_eq_tree,markedConnectionPolynomial_eq_tree]
  apply hbound.trans_eq
  field_simp [hh.1.ne',hq.1.ne',(sub_pos.mpr hq.2).ne']
  ring

theorem finiteClusterTail_eq_restricted_volume [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    finiteClusterTail G Q x n p =
      (law p).real {ω | ω ∩ (Q : Set E) ∈ volumeEvent G x n} := by
  let f (ω : Set E) : ℝ := if n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard then 1 else 0
  have hf : ∀ ω, f ω = f (ω ∩ (Q : Set E)) := by
    intro ω
    simp only [f,Set.inter_assoc,Set.inter_self]
  have he : (∫ ω, f ω ∂law p) = finiteClusterTail G Q x n p := by
    rw [integral_eq_bernoulliPolynomial Q p f hf]
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [f,finiteClusterTailIndicator,
      Set.inter_eq_left.mpr (show (ω : Set E) ⊆ Q from hω),
      ←coe_finiteRootComponent,Set.ncard_coe_finset]
  rw [←he]
  have hset : MeasurableSet {ω : Set E | ω ∩ (Q : Set E) ∈ volumeEvent G x n} := by
    exact (measurableSet_volumeEvent G x n).preimage (measurable_inter_const _)
  rw [←integral_event_indicator p _ hset]
  apply integral_congr_ae
  filter_upwards with ω
  have hfinite := cluster_finite_of_finite_edges G
    (ω := ω ∩ (Q : Set E)) (Q.finite_toSet.subset Set.inter_subset_right) x
  have hiff : ω ∩ (Q : Set E) ∈ volumeEvent G x n ↔
      n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard := by
    change (n : ℕ∞) ≤ (cluster G (ω ∩ (Q : Set E)) x).encard ↔ _
    rw [←hfinite.cast_ncard_eq]
    exact_mod_cast Iff.rfl
  simp only [f,hiff]

theorem finiteWitness_restricted_probability_tendsto [Encodable E]
    (A : Set (Set E)) (hA : IsUpperSet A) (hf : FiniteWitness A) (p : unitInterval) :
    Tendsto (fun k => (law p).real {ω : Set E |
      ω ∩ (edgeExhaustion (E := E) k : Set E) ∈ A}) atTop (𝓝 ((law p).real A)) := by
  have hmono : Monotone (fun k => {ω : Set E |
      ω ∩ (edgeExhaustion (E := E) k : Set E) ∈ A}) := by
    intro k l h ω hω
    exact hA (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
  have hh := tendsto_measure_iUnion_atTop (μ := law p) hmono
  rw [←witness_eq_union A hA hf] at hh
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hh

theorem volumeEvent_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (volumeEvent G x n) := by
  rw [volumeEvent_eq_clusterLarge G x n]
  exact clusterLarge_upper G x n

theorem volumeEvent_finiteWitness (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (volumeEvent G x n) := by
  rw [volumeEvent_eq_clusterLarge G x n]
  exact finiteWitness_clusterLarge G x n

theorem volume_probability_le_of_finite_tails [Countable E]
    (G : BondGraph V E) (x : V) (n : ℕ) (p : unitInterval) (B : ℝ)
    (hB : ∀ Q : Finset E, finiteClusterTail G Q x n p ≤ B) :
    (law p).real (volumeEvent G x n) ≤ B := by
  let : Encodable E := Encodable.ofCountable E
  have hr := finiteWitness_restricted_probability_tendsto (volumeEvent G x n)
    (volumeEvent_upper G x n) (volumeEvent_finiteWitness G x n) p
  have hseq (k : ℕ) : (law p).real {ω : Set E |
      ω ∩ (edgeExhaustion (E := E) k : Set E) ∈ volumeEvent G x n} ≤ B :=
    (finiteClusterTail_eq_restricted_volume G (edgeExhaustion (E := E) k) x n p).symm.le.trans (hB _)
  exact le_of_tendsto hr (Eventually.of_forall hseq)

theorem percolationProbability_le_of_marked_bounds [Countable E]
    (G : BondGraph V E) (x : V) (p h : unitInterval) (hh : 0 < (h : ℝ)) (B : ℝ)
    (hB : ∀ Q : Finset E, markedConnectionPolynomial G Q x h p ≤ B) :
    percolationProbability G p x ≤ 2 * B := by
  obtain ⟨n,hn⟩ := exists_nat_ge (1 / (h : ℝ))
  have hprod : 1 ≤ (h : ℝ) * n := by
    have he := (div_le_iff₀ hh).mp hn
    linarith
  apply (measureReal_mono (μ := law p) (h₂ := measure_ne_top _ _) ?_).trans
    (volume_probability_le_of_finite_tails G x n p (2 * B) (fun Q =>
      (finiteClusterTail_le_markedConnection G Q x n p h hprod).trans
        (mul_le_mul_of_nonneg_left (hB Q) (by norm_num : (0 : ℝ) ≤ 2))))
  intro ω hω
  change (n : ℕ∞) ≤ (cluster G ω x).encard
  rw [Set.encard_eq_top hω]
  exact le_top

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ProbabilityUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem markedConnection_entropy_uniform
    (G : BondGraph V E) (Q : Finset E) (x : V) (p q h : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) (hq : (q : ℝ) ∈ Set.Ioo 0 1)
    (hh : (h : ℝ) ∈ Set.Ioo 0 1) (d : ℕ)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (D : ℝ) (hD : 0 < D) (hden : D ≤ (q : ℝ) * (1-q))
    (hsmall : ((p : ℝ) - q) ^ 2 ≤ h) :
    markedConnectionPolynomial G Q x h q ≤
      (2 + 2 * (d : ℝ) / D) * markedConnectionPolynomial G Q x h p := by
  apply (markedConnection_entropy_comparison G Q x p q h hp hq hh d hdeg).trans
  apply mul_le_mul_of_nonneg_right _ (by
    rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg p h _)
  apply add_le_add_right
  have hd : 0 ≤ 2 * (d : ℝ) := by positivity
  have hden0 : 0 < (q : ℝ) * (1-q) := hD.trans_le hden
  calc
    2 * (d : ℝ) * ((p : ℝ) - q) ^ 2 / ((q : ℝ) * (1-q) * h) ≤
        2 * (d : ℝ) * h / ((q : ℝ) * (1-q) * h) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hd)
        (mul_nonneg hden0.le hh.1.le)
    _ = 2 * (d : ℝ) / ((q : ℝ) * (1-q)) := by field_simp [hh.1.ne']
    _ ≤ 2 * (d : ℝ) / D := div_le_div_of_nonneg_left hd hD hden

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SmallWitness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe v
variable {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem small_witness_derivative_bound (Q : Finset E) (A : Finset E → Prop)
    (hmono : ∀ ω η, ω ⊆ η → A ω → A η) (r : ℕ)
    (hcert : ∀ ω ⊆ Q, A ω → ∃ s ⊆ ω, s.card ≤ r ∧ ∀ η, s ⊆ η → A η)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    p * deriv (bernoulliPolynomial Q (fun ω => if A ω then 1 else 0)) p ≤
      (r : ℝ) * bernoulliPolynomial Q (fun ω => if A ω then 1 else 0) p := by
  let f : Finset E → ℝ := fun ω => if A ω then 1 else 0
  have hrusso : p * deriv (bernoulliPolynomial Q f) p =
      bernoulliPolynomial Q (fun ω => ∑ e ∈ Q,
        if e ∈ ω then f ω - f (ω.erase e) else 0) p := by
    rw [(hasDerivAt_bernoulliPolynomial Q f p).deriv, Finset.mul_sum,
      bernoulliPolynomial_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact (bernoulliPolynomial_open_difference Q e he f p).symm
  change p * deriv (bernoulliPolynomial Q f) p ≤
    (r : ℝ) * bernoulliPolynomial Q f p
  rw [hrusso, ←bernoulliPolynomial_const_mul]
  apply bernoulliPolynomial_mono Q _ _ p hp
  intro ω hω
  by_cases hA : A ω
  · obtain ⟨s,hs,hsr,hsa⟩ := hcert ω hω hA
    calc
      _ ≤ ∑ e ∈ Q, if e ∈ s then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro e he
        by_cases hes : e ∈ s
        · by_cases heω : e ∈ ω <;> by_cases herase : A (ω.erase e) <;>
            simp [f,hA,hes,heω,herase]
        · have herase : A (ω.erase e) := hsa _ (by
            intro a ha
            exact Finset.mem_erase.mpr ⟨fun hae => hes (hae ▸ ha),hs ha⟩)
          simp [f,hA,hes,herase]
      _ = ((Q.filter (fun e => e ∈ s)).card : ℝ) := by
        rw [Finset.card_filter, Nat.cast_sum]
        simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      _ ≤ (s.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (show Q.filter (fun e => e ∈ s) ⊆ s from
          fun e he => (Finset.mem_filter.mp he).2)
      _ ≤ (r : ℝ) * f ω := by simpa [f,hA] using (show (s.card : ℝ) ≤ r by exact_mod_cast hsr)
  · have herase (e : E) : ¬ A (ω.erase e) := fun h =>
      hA (hmono _ _ (Finset.erase_subset e ω) h)
    simp [f,hA,herase]

theorem small_witness_probability_transfer (Q : Finset E) (A : Finset E → Prop)
    (hmono : ∀ ω η, ω ⊆ η → A ω → A η) (r : ℕ)
    (hcert : ∀ ω ⊆ Q, A ω → ∃ s ⊆ ω, s.card ≤ r ∧ ∀ η, s ⊆ η → A η)
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : p ≤ q) :
    bernoulliPolynomial Q (fun ω => if A ω then 1 else 0) q ≤
      Real.exp ((r : ℝ) / p * ((q : ℝ) - p)) *
        bernoulliPolynomial Q (fun ω => if A ω then 1 else 0) p := by
  let H := bernoulliPolynomial Q (fun ω => if A ω then (1 : ℝ) else 0)
  apply exponential_transfer_of_deriv_bound H p q ((r : ℝ) / p)
    (fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt) hpq
  intro t ht
  have ht0 : 0 < t := hp.trans_le ht.1
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le,ht.2.trans q.2.2⟩
  have hb := small_witness_derivative_bound Q A hmono r hcert t htI
  have hH : 0 ≤ H t := bernoulliPolynomial_nonneg Q _ t htI (fun ω _ => by split <;> positivity)
  calc
    deriv H t ≤ (r : ℝ) * H t / t := (le_div_iff₀ ht0).mpr (by simpa only [mul_comm t] using hb)
    _ ≤ (r : ℝ) * H t / p := div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg r) hH) hp ht.1
    _ = _ := by ring

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicBallGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicBall_small_witness (G : BondGraph V E) (S : Set E)
    (x y : V) (r : ℕ) (ω : Finset E)
    (hy : y ∈ intrinsicBall G ((ω : Set E) ∩ S) x r) :
    ∃ s ⊆ ω, s.card ≤ r ∧ ∀ η : Finset E, s ⊆ η →
      y ∈ intrinsicBall G ((η : Set E) ∩ S) x r := by
  obtain ⟨l,hl,hlen,ho⟩ := hy
  refine ⟨l.toFinset, ?_, l.toFinset_card_le.trans hlen, ?_⟩
  · intro e he
    exact (ho e (List.mem_toFinset.mp he)).1
  · intro η hη
    exact ⟨l,hl,hlen,fun e he => ⟨hη (List.mem_toFinset.mpr he),(ho e he).2⟩⟩

theorem intrinsicBallPolynomial_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x y : V) (r : ℕ) (p : unitInterval) :
    intrinsicBallPolynomial G hloc S x y r p =
      (law p {ω | y ∈ intrinsicBall G (ω ∩ S) x r}).toReal := by
  change finiteEventPolynomial (intrinsicBondSupport G hloc S x r)
    {ω | y ∈ intrinsicBall G (ω ∩ S) x r} p = _
  rw [finiteEventPolynomial_restrict]
  congr 2
  ext ω
  have hsub : (intrinsicBondSupport G hloc S x r : Set E) ⊆ S := by
    rw [intrinsicBondSupport_coe]; exact Set.inter_subset_right
  change (y ∈ intrinsicBall G ((ω ∩ _) ∩ S) x r) ↔ _
  rw [Set.inter_assoc,Set.inter_eq_left.mpr hsub,intrinsicBall_domain_restrict]

theorem intrinsicBall_probability_transfer (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Set E) (x y : V) (r : ℕ)
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : p ≤ q) :
    intrinsicBallPolynomial G hloc S x y r q ≤
      Real.exp ((r : ℝ) / p * ((q : ℝ) - p)) *
        intrinsicBallPolynomial G hloc S x y r p := by
  apply small_witness_probability_transfer _ _ _ r _ p q hp hpq
  · intro ω η hωη hy
    exact intrinsicBall_mono G (Set.inter_subset_inter_left S
      (show (ω : Set E) ⊆ η from hωη)) x r hy
  · intro ω _ hy
    exact intrinsicBall_small_witness G S x y r ω hy

theorem intrinsicBallMoment_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (S : Set E) (x : V) (r : ℕ) (p : unitInterval) (hp : p < pc G) :
    intrinsicBallMoment G hloc S x r p ≤ susceptibility G p x := by
  apply (Finset.sum_le_sum (fun y _ => ?_)).trans
    ((summable_twoPoint_subcritical G hloc hqt p hp x).sum_le_tsum _
      (fun y _ => twoPoint_nonneg G p x y))
  rw [intrinsicBallPolynomial_eq]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  rintro ω ⟨l,hl,_,ho⟩
  exact hl.conn (fun e he => (ho e he).1)

theorem intrinsicBallMoment_transfer (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (r : ℕ) (p q : unitInterval)
    (hp : 0 < (p : ℝ)) (hpq : p ≤ q) :
    intrinsicBallMoment G hloc S x r q ≤
      Real.exp ((r : ℝ) / p * ((q : ℝ) - p)) *
        intrinsicBallMoment G hloc S x r p := by
  unfold intrinsicBallMoment
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y _ => intrinsicBall_probability_transfer G hloc S x y r p q hp hpq)

theorem intrinsicBall_ncard_eq_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (r : ℕ) :
    ((intrinsicBall G ω x r).ncard : ℝ) =
      ∑ y ∈ (finite_reachBall hloc x r).toFinset,
        if y ∈ intrinsicBall G ω x r then (1 : ℝ) else 0 := by
  let B := (finite_reachBall hloc x r).toFinset.filter (fun y => y ∈ intrinsicBall G ω x r)
  have he : (B : Set V) = intrinsicBall G ω x r := by
    ext y
    simp only [B,Finset.mem_coe,Finset.mem_filter]
    exact and_iff_right_of_imp (fun hy => (finite_reachBall hloc x r).mem_toFinset.mpr
      (intrinsicBall_subset_reachBall G ω x r hy))
  rw [←he,Set.ncard_coe_finset]
  change (B.card : ℝ) = _
  rw [Finset.card_filter,Nat.cast_sum]
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [he]

theorem measurableSet_mem_intrinsicBall_domain (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Set E) (x y : V) (r : ℕ) :
    MeasurableSet {ω | y ∈ intrinsicBall G (ω ∩ S) x r} := by
  let Q := intrinsicBondSupport G hloc S x r
  have he : {ω | y ∈ intrinsicBall G (ω ∩ S) x r} =
      {ω | ω ∩ (Q : Set E) ∈ {η | y ∈ intrinsicBall G (η ∩ S) x r}} := by
    ext ω
    have hsub : (Q : Set E) ⊆ S := by
      dsimp [Q]; rw [intrinsicBondSupport_coe]; exact Set.inter_subset_right
    change (y ∈ intrinsicBall G (ω ∩ S) x r) ↔
      (y ∈ intrinsicBall G ((ω ∩ (Q : Set E)) ∩ S) x r)
    rw [Set.inter_assoc,Set.inter_eq_left.mpr hsub,intrinsicBall_domain_restrict]
  rw [he]
  exact measurableSet_finite_restriction Q _

theorem integral_intrinsicBall_ncard_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (r : ℕ) (p : unitInterval) :
    (∫ ω, ((intrinsicBall G (ω ∩ S) x r).ncard : ℝ) ∂law p) =
      intrinsicBallMoment G hloc S x r p := by
  simp_rw [intrinsicBall_ncard_eq_sum G hloc]
  rw [integral_finsetSum]
  · unfold intrinsicBallMoment
    apply Finset.sum_congr rfl
    intro y _
    rw [intrinsicBallPolynomial_eq]
    have heq : (fun ω : Set E => if y ∈ intrinsicBall G (ω ∩ S) x r then (1 : ℝ) else 0) =
        {ω | y ∈ intrinsicBall G (ω ∩ S) x r}.indicator 1 := by
      funext ω
      by_cases hy : y ∈ intrinsicBall G (ω ∩ S) x r <;> simp [Set.indicator,hy]
    rw [heq,integral_indicator_one (measurableSet_mem_intrinsicBall_domain G hloc S x y r)]
    rfl
  · intro y _
    have heq : (fun ω : Set E => if y ∈ intrinsicBall G (ω ∩ S) x r then (1 : ℝ) else 0) =
        {ω | y ∈ intrinsicBall G (ω ∩ S) x r}.indicator (fun _ => 1) := by
      funext ω
      by_cases hy : y ∈ intrinsicBall G (ω ∩ S) x r <;> simp [Set.indicator,hy]
    rw [heq]
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_mem_intrinsicBall_domain G hloc S x y r)

theorem integrable_intrinsicBall_ncard (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (r : ℕ) (p : unitInterval) :
    Integrable (fun ω => ((intrinsicBall G (ω ∩ S) x r).ncard : ℝ)) (law p) := by
  simp_rw [intrinsicBall_ncard_eq_sum G hloc]
  apply integrable_finsetSum
  intro y _
  have heq : (fun ω : Set E => if y ∈ intrinsicBall G (ω ∩ S) x r then (1 : ℝ) else 0) =
      {ω | y ∈ intrinsicBall G (ω ∩ S) x r}.indicator (fun _ => 1) := by
    funext ω
    by_cases hy : y ∈ intrinsicBall G (ω ∩ S) x r <;> simp [Set.indicator,hy]
  rw [heq]
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_mem_intrinsicBall_domain G hloc S x y r)

theorem critical_intrinsicBallMoment_linear [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (A : ℝ) (hA : 0 < A)
    (hχ : ∀ p : unitInterval, p < pc G → ∀ x,
      susceptibility G p x ≤ A / ((pc G : ℝ) - p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Set E) x (r : ℕ), 0 < r →
      intrinsicBallMoment G hloc S x r (pc G) ≤ C * r := by
  have hpc : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  refine ⟨2 * Real.exp 1 * A / (pc G : ℝ),by positivity,fun S x r hr => ?_⟩
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  let p : unitInterval := ⟨(pc G : ℝ) * r / (r+1), by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < r+1)).mpr
      have hc := mul_le_mul_of_nonneg_right (pc G).2.2 hrR.le
      nlinarith⟩
  have hp0 : 0 < (p : ℝ) := by dsimp [p]; positivity
  have hp : p < pc G := by
    change (pc G : ℝ) * r / (r+1) < (pc G : ℝ)
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < r+1)).mpr
    nlinarith
  have hgap : (pc G : ℝ) - p = (pc G : ℝ) / (r+1) := by dsimp [p]; field_simp; ring
  have hexp : (r : ℝ) / p * ((pc G : ℝ) - p) = 1 := by
    rw [hgap]
    dsimp [p]
    field_simp
  calc
    _ ≤ Real.exp ((r : ℝ) / p * ((pc G : ℝ) - p)) *
        intrinsicBallMoment G hloc S x r p := intrinsicBallMoment_transfer G hloc S x r p (pc G) hp0 hp.le
    _ ≤ Real.exp 1 * (A / ((pc G : ℝ) - p)) := by
      rw [hexp]
      exact mul_le_mul_of_nonneg_left
        ((intrinsicBallMoment_le_susceptibility G hloc hqt S x r p hp).trans (hχ p hp x))
        (Real.exp_pos 1).le
    _ = Real.exp 1 * A / (pc G : ℝ) * (r+1) := by rw [hgap]; field_simp
    _ ≤ _ := by
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hn : 0 ≤ Real.exp 1 * A / (pc G : ℝ) := by positivity
      calc
        _ ≤ (Real.exp 1 * A / (pc G : ℝ)) * (2*r) :=
          mul_le_mul_of_nonneg_left (by linarith) hn
        _ = _ := by ring

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicBallExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicBall_mono_radius (G : BondGraph V E) (ω : Set E) (x : V)
    {m n : ℕ} (hmn : m ≤ n) : intrinsicBall G ω x m ⊆ intrinsicBall G ω x n := by
  rintro y ⟨l,hl,hlen,ho⟩
  exact ⟨l,hl,hlen.trans hmn,ho⟩

theorem along_open_of_agree_intrinsic_prefix (G : BondGraph V E)
    (ω η : Set E) (x y : V) (n : ℕ) (l : List E) (hl : Along G x l y)
    (hlen : l.length ≤ n) (ho : ∀ e ∈ l, e ∈ η)
    (hagree : ∀ e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)), e ∈ ω ↔ e ∈ η) :
    ∀ e ∈ l, e ∈ ω := by
  rcases hl.first_outside ω with h | ⟨a,b,e,l₁,l₂,heq,h₁,he,_,hprefix,hnot⟩
  · exact h
  · exfalso
    have hlength : l₁.length ≤ n-1 := by
      rw [heq,List.length_append,List.length_cons] at hlen
      omega
    have ha : a ∈ intrinsicBall G ω x (n-1) := ⟨l₁,h₁,hlength,hprefix⟩
    have hei : e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)) :=
      ⟨a,ha,by simp [he]⟩
    exact hnot ((hagree e hei).mpr (ho e (by rw [heq]; simp)))

theorem along_bonds_incident_intrinsic_prefix (G : BondGraph V E)
    (ω : Set E) (x y : V) (n : ℕ) (l : List E) (hl : Along G x l y)
    (hlen : l.length ≤ n) (ho : ∀ e ∈ l, e ∈ ω) :
    ∀ e ∈ l, e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)) := by
  rcases hl.first_outside (ballIncidentEdges G (intrinsicBall G ω x (n-1))) with
    h | ⟨a,b,e,l₁,l₂,heq,h₁,he,_,_,hnot⟩
  · exact h
  · exfalso
    have hlength : l₁.length ≤ n-1 := by
      rw [heq,List.length_append,List.length_cons] at hlen
      omega
    have ha : a ∈ intrinsicBall G ω x (n-1) := ⟨l₁,h₁,hlength,fun f hf => ho f (by rw [heq]; simp [hf])⟩
    exact hnot ⟨a,ha,by simp [he]⟩

theorem intrinsicBall_eq_of_incident_agreement (G : BondGraph V E)
    (ω η : Set E) (x : V) (n : ℕ)
    (hagree : ∀ e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)), e ∈ ω ↔ e ∈ η) :
    intrinsicBall G ω x n = intrinsicBall G η x n := by
  apply Set.Subset.antisymm
  · rintro y ⟨l,hl,hlen,ho⟩
    exact ⟨l,hl,hlen,fun e he => (hagree e
      (along_bonds_incident_intrinsic_prefix G ω x y n l hl hlen ho e he)).mp (ho e he)⟩
  · rintro y ⟨l,hl,hlen,ho⟩
    exact ⟨l,hl,hlen,along_open_of_agree_intrinsic_prefix G ω η x y n l hl hlen ho hagree⟩

theorem intrinsicBall_history_eq_of_incident_agreement (G : BondGraph V E)
    (ω η : Set E) (x : V) (n : ℕ)
    (hagree : ∀ e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)), e ∈ ω ↔ e ∈ η) :
    ∀ i ≤ n, intrinsicBall G ω x i = intrinsicBall G η x i := by
  intro i hi
  apply intrinsicBall_eq_of_incident_agreement G ω η x i
  rintro e ⟨a,ha,he⟩
  exact hagree e ⟨a,intrinsicBall_mono_radius G ω x (by omega) ha,he⟩

theorem measurableSet_intrinsicBall_eq [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V) (n : ℕ) (B : Set V) :
    MeasurableSet {ω | intrinsicBall G (ω ∩ S) x n = B} := by
  have he : {ω | intrinsicBall G (ω ∩ S) x n = B} =
      ⋂ y : V, {ω | y ∈ intrinsicBall G (ω ∩ S) x n ↔ y ∈ B} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact Set.ext_iff
  rw [he]
  exact MeasurableSet.iInter (fun y =>
    ((measurableSet_mem_intrinsicBall_domain G hloc S x y n).mem.iff measurable_const).setOf)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_intrinsic_distance_eq (G : BondGraph V E) (ω : Set E)
    (x y : V) (hc : Conn G ω x y) (n : ℕ)
    (hn : n ≤ (openSimpleGraph G ω).dist x y) :
    ∃ z, Conn G ω x z ∧ (openSimpleGraph G ω).dist x z = n := by
  obtain ⟨w,hw⟩ := ((conn_iff_reachable G ω x y).mp hc).exists_walk_length_eq_dist
  have hshort := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_take n)
  have hlen : (w.take n).length = n := by
    rw [SimpleGraph.Walk.take_length,Nat.min_eq_left (by omega)]
  exact ⟨w.getVert n,(conn_iff_reachable G ω x _).mpr (w.take n).reachable,
    hshort.symm.trans hlen⟩

theorem intrinsicRadiusEvent_iff_sphere (G : BondGraph V E) (ω : Set E)
    (x : V) (n : ℕ) :
    ω ∈ intrinsicRadiusEvent G x n ↔ (intrinsicSphere G ω x n).Nonempty := by
  constructor
  · rintro ⟨y,hc,hn⟩
    exact exists_intrinsic_distance_eq G ω x y hc n hn
  · rintro ⟨y,hc,hn⟩
    exact ⟨y,hc,hn.ge⟩

theorem intrinsicSphere_eq_ball_sdiff (G : BondGraph V E) (ω : Set E)
    (x : V) (n : ℕ) (hn : 0 < n) :
    intrinsicSphere G ω x n = intrinsicBall G ω x n \ intrinsicBall G ω x (n-1) := by
  ext y
  constructor
  · rintro ⟨hc,hd⟩
    refine ⟨(intrinsicBall_iff_distance_le G ω x y n hc).mpr hd.le,?_⟩
    rw [intrinsicBall_iff_distance_le G ω x y (n-1) hc,hd]
    omega
  · rintro ⟨hy,hnot⟩
    obtain ⟨l,hl,hlen,ho⟩ := hy
    have hc := hl.conn ho
    have hle := (intrinsicBall_iff_distance_le G ω x y n hc).mp ⟨l,hl,hlen,ho⟩
    rw [intrinsicBall_iff_distance_le G ω x y (n-1) hc] at hnot
    exact ⟨hc,by omega⟩

theorem intrinsicSphere_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (n : ℕ) : (intrinsicSphere G ω x n).Finite := by
  apply (finite_reachBall hloc x n).subset
  rintro y ⟨hc,hd⟩
  exact intrinsicBall_subset_reachBall G ω x n
    ((intrinsicBall_iff_distance_le G ω x y n hc).mpr hd.le)

theorem intrinsicSphere_disjoint (G : BondGraph V E) (ω : Set E) (x : V)
    {m n : ℕ} (hmn : m ≠ n) : Disjoint (intrinsicSphere G ω x m) (intrinsicSphere G ω x n) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨_,hm⟩ ⟨_,hn⟩
  exact hmn (hm.symm.trans hn)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicFreshPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem shortest_drop_support_distance (G : BondGraph V E) (ω : Set E)
    {x y : V} (w : (openSimpleGraph G ω).Walk x y)
    (hw : w.length = (openSimpleGraph G ω).dist x y)
    (j : ℕ) (hj : j ≤ w.length) (z : V) (hz : z ∈ (w.drop j).support) :
    j ≤ (openSimpleGraph G ω).dist x z := by
  let k := (w.drop j).support.idxOf z
  have hk : k ≤ (w.drop j).length := by
    have hh := List.idxOf_lt_length_of_mem hz
    rw [SimpleGraph.Walk.length_support] at hh
    exact Nat.le_of_lt_succ hh
  have hkj : j+k ≤ w.length := by
    rw [SimpleGraph.Walk.drop_length] at hk
    omega
  have hget : w.getVert (j+k) = z := by
    rw [←SimpleGraph.Walk.drop_getVert]
    exact (w.drop j).getVert_support_idxOf hz
  have hshort := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_take (j+k))
  rw [SimpleGraph.Walk.take_length,Nat.min_eq_left hkj,hget] at hshort
  omega

theorem intrinsic_long_connection_fresh (G : BondGraph V E) (ω : Set E)
    (x y : V) (j r : ℕ) (hj : 0 < j) (hc : Conn G ω x y)
    (hlen : j+r ≤ (openSimpleGraph G ω).dist x y) :
    ∃ z ∈ intrinsicSphere G ω x j,
      Conn G (ω \ ballIncidentEdges G (intrinsicBall G ω x (j-1))) z y ∧
      r ≤ (openSimpleGraph G (ω \ ballIncidentEdges G (intrinsicBall G ω x (j-1)))).dist z y := by
  obtain ⟨w,hw⟩ := ((conn_iff_reachable G ω x y).mp hc).exists_walk_length_eq_dist
  have hjw : j ≤ w.length := by omega
  have hzdist : (openSimpleGraph G ω).dist x (w.getVert j) = j := by
    have hh := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_take j)
    rw [SimpleGraph.Walk.take_length,Nat.min_eq_left hjw] at hh
    exact hh.symm
  have hz : w.getVert j ∈ intrinsicSphere G ω x j :=
    ⟨(conn_iff_reachable G ω x _).mpr (w.take j).reachable,hzdist⟩
  let Q := ballIncidentEdges G (intrinsicBall G ω x (j-1))
  have hsupport (z : V) (hz : z ∈ (w.drop j).support) : z ∉ intrinsicBall G ω x (j-1) := by
    intro hzB
    have hdist := shortest_drop_support_distance G ω w hw j hjw z hz
    obtain ⟨l,hl,hlen,ho⟩ := hzB
    have hle := (intrinsicBall_iff_distance_le G ω x z (j-1) (hl.conn ho)).mp ⟨l,hl,hlen,ho⟩
    omega
  have hedges : ∀ e, e ∈ (w.drop j).edges → e ∈ (openSimpleGraph G (ω \ Q)).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : (openSimpleGraph G ω).Adj a b := by
        simpa using (w.drop j).edges_subset_edgeSet he
      obtain ⟨hne,f,hf,hfab⟩ := hab
      have hnot : f ∉ Q := by
        rintro ⟨z,hzB,hzf⟩
        rw [hfab] at hzf
        rcases (show z = a ∨ z = b from by simpa only [Sym2.mem_iff] using hzf) with hza | hzb
        · exact hsupport a ((w.drop j).fst_mem_support_of_mem_edges he) (hza ▸ hzB)
        · exact hsupport b ((w.drop j).snd_mem_support_of_mem_edges he) (hzb ▸ hzB)
      show (openSimpleGraph G (ω \ Q)).Adj a b
      exact ⟨hne,f,⟨hf,hnot⟩,hfab⟩
  let w' := (w.drop j).transfer (openSimpleGraph G (ω \ Q)) hedges
  have hc' : Conn G (ω \ Q) (w.getVert j) y := (conn_iff_reachable G _ _ _).mpr w'.reachable
  have hle : (openSimpleGraph G ω).dist (w.getVert j) y ≤
      (openSimpleGraph G (ω \ Q)).dist (w.getVert j) y := by
    apply SimpleGraph.Reachable.dist_anti (G := openSimpleGraph G (ω \ Q))
      (G' := openSimpleGraph G ω) _ w'.reachable
    intro a b hab
    obtain ⟨hne,e,he,heq⟩ := hab
    exact ⟨hne,e,he.1,heq⟩
  have hdrop := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_drop j)
  rw [SimpleGraph.Walk.drop_length] at hdrop
  refine ⟨w.getVert j,hz,hc',?_⟩
  change r ≤ (openSimpleGraph G (ω \ Q)).dist (w.getVert j) y
  omega

theorem intrinsic_radius_fresh_continuation (G : BondGraph V E) (ω : Set E)
    (x : V) (j r : ℕ) (hj : 0 < j)
    (hR : ω ∈ intrinsicRadiusEvent G x (j+r)) :
    ∃ z ∈ intrinsicSphere G ω x j,
      ω \ ballIncidentEdges G (intrinsicBall G ω x (j-1)) ∈ intrinsicRadiusEvent G z r := by
  obtain ⟨y,hc,hlen⟩ := hR
  obtain ⟨z,hz,hconn,hdist⟩ := intrinsic_long_connection_fresh G ω x y j r hj hc hlen
  exact ⟨z,hz,y,hconn,hdist⟩

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ThinSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_thin_intrinsicSphere (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (r k : ℕ) (hf : (cluster G ω x).Finite)
    (hsmall : (cluster G ω x).ncard < (r+1)*(k+1)) :
    ∃ j ∈ Finset.Icc r (2*r), (intrinsicSphere G ω x j).ncard ≤ k := by
  by_contra hnot
  push Not at hnot
  let F : ℕ → Finset V := fun j => (intrinsicSphere_finite G hloc ω x j).toFinset
  have hdisj : (↑(Finset.Icc r (2*r)) : Set ℕ).PairwiseDisjoint F := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro y hi hj
    exact Set.disjoint_left.mp (intrinsicSphere_disjoint G ω x hij)
      ((intrinsicSphere_finite G hloc ω x i).mem_toFinset.mp hi)
      ((intrinsicSphere_finite G hloc ω x j).mem_toFinset.mp hj)
  have hsub : (Finset.Icc r (2*r)).biUnion F ⊆ hf.toFinset := by
    intro y hy
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hy
    exact hf.mem_toFinset.mpr ((intrinsicSphere_finite G hloc ω x j).mem_toFinset.mp hj).1
  have hcards := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcards
  have hlo : (r+1)*(k+1) ≤ ∑ j ∈ Finset.Icc r (2*r), (F j).card := by
    calc
      _ = ∑ j ∈ Finset.Icc r (2*r), (k+1) := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.card_Icc]
        have he : 2*r+1-r = r+1 := by omega
        rw [he]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => by
        have h := hnot j hj
        change k < (intrinsicSphere G ω x j).ncard at h
        rw [Set.ncard_eq_toFinset_card _ (intrinsicSphere_finite G hloc ω x j)] at h
        exact h)
  have he : hf.toFinset.card = (cluster G ω x).ncard := (Set.ncard_eq_toFinset_card _ hf).symm
  rw [he] at hcards
  omega

theorem thinSphereCell_pairwise (G : BondGraph V E) (S : Set E) (x : V) (r k : ℕ) :
    Pairwise (fun a b : ℕ × Finset V × Finset V =>
      Disjoint (thinSphereCell G S x r k a.1 a.2.1 a.2.2)
        (thinSphereCell G S x r k b.1 b.2.1 b.2.2)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro ω ha hb
  have hj : a.1 = b.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (not_lt_of_ge ha.2.2.2.2.1) (hb.2.2.2.2.2 a.1 ha.1 h)
    · exact (not_lt_of_ge hb.2.2.2.2.1) (ha.2.2.2.2.2 b.1 hb.1 h)
  have hU : a.2.1 = b.2.1 := by
    apply Finset.coe_injective
    have haU : intrinsicBall G (ω ∩ S) x (b.1-1) = (a.2.1 : Set V) := by
      simpa only [hj] using ha.2.2.1
    exact haU.symm.trans hb.2.2.1
  have hW : a.2.2 = b.2.2 := by
    apply Finset.coe_injective
    have haW : intrinsicBall G (ω ∩ S) x b.1 = (a.2.2 : Set V) := by
      simpa only [hj] using ha.2.2.2.1
    exact haW.symm.trans hb.2.2.2.1
  exact hab (Prod.ext hj (Prod.ext hU hW))

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ThinSphereExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_finite_local_nat (Q : Finset E) (f : Set E → ℕ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Measurable f := by
  let g : Set (Q : Set E) → ℕ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  rw [he]
  exact (measurable_of_finite g).comp (measurable_set_restrict (Q : Set E))

theorem measurable_intrinsicSphere_ncard (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (n : ℕ) (hn : 0 < n) :
    Measurable (fun ω => (intrinsicSphere G (ω ∩ S) x n).ncard) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x n).toFinset
  apply measurable_finite_local_nat Q
  intro ω
  have hballs := intrinsicBall_history_eq_of_incident_agreement G
    (ω ∩ S) ((ω ∩ (Q : Set E)) ∩ S) x n (by
      rintro e ⟨a,ha,he⟩
      have haR : a ∈ reachBall G x n := reachBall_mono G x (Nat.sub_le n 1)
        (intrinsicBall_subset_reachBall G (ω ∩ S) x (n-1) ha)
      have heQ : e ∈ Q := (mem_incidentSupport G hloc _ e).mpr
        ⟨a,(finite_reachBall hloc x n).mem_toFinset.mpr haR,he⟩
      simp only [Set.mem_inter_iff,Finset.mem_coe,heQ,and_true])
  rw [intrinsicSphere_eq_ball_sdiff G _ x n hn,intrinsicSphere_eq_ball_sdiff G _ x n hn,
    hballs n le_rfl,hballs (n-1) (Nat.sub_le n 1)]

theorem thinSphereCell_dependsOn (G : BondGraph V E) (S : Set E) (x : V)
    (r k j : ℕ) (hr : 0 < r) (U W : Finset V) :
    DependsOn
      (fun ω => ω ∈ thinSphereCell G S x r k j U W) (ballIncidentEdges G U) := by
  intro ω η hagree
  apply propext
  have hforward (ω η : Set E)
      (hωη : ∀ e ∈ ballIncidentEdges G U, e ∈ ω ↔ e ∈ η)
      (hω : ω ∈ thinSphereCell G S x r k j U W) :
      η ∈ thinSphereCell G S x r k j U W := by
    obtain ⟨hrj,hj2,hU,hW,hthin,hfirst⟩ := hω
    have hballs := intrinsicBall_history_eq_of_incident_agreement G (ω ∩ S) (η ∩ S) x j (by
      intro e he
      rw [hU] at he
      exact and_congr (hωη e he) Iff.rfl)
    have hspheres (i : ℕ) (hi : r ≤ i) (hij : i ≤ j) :
        intrinsicSphere G (ω ∩ S) x i = intrinsicSphere G (η ∩ S) x i := by
      have hi0 : 0 < i := hr.trans_le hi
      rw [intrinsicSphere_eq_ball_sdiff G _ x i hi0,intrinsicSphere_eq_ball_sdiff G _ x i hi0,
        hballs i hij,hballs (i-1) ((Nat.sub_le i 1).trans hij)]
    refine ⟨hrj,hj2,(hballs (j-1) (Nat.sub_le j 1)).symm.trans hU,
      (hballs j le_rfl).symm.trans hW,?_,?_⟩
    · rw [←hspheres j hrj le_rfl]
      exact hthin
    · intro i hi hij
      rw [←hspheres i hi hij.le]
      exact hfirst i hi hij
  exact ⟨hforward ω η (fun e he => (hagree e he).to_iff),
    hforward η ω (fun e he => (hagree e he).symm.to_iff)⟩

theorem measurableSet_thinSphereCell [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V)
    (r k j : ℕ) (hr : 0 < r) (U W : Finset V) :
    MeasurableSet (thinSphereCell G S x r k j U W) := by
  by_cases hrj : r ≤ j
  · have hj0 : 0 < j := hr.trans_le hrj
    have hfirst : Measurable (fun ω : Set E => ∀ i, r ≤ i → i < j →
        k < (intrinsicSphere G (ω ∩ S) x i).ncard) := by
      apply Measurable.forall
      intro i
      by_cases hri : r ≤ i
      · exact measurable_const.imp (measurable_const.imp
          (measurable_const.lt (measurable_intrinsicSphere_ncard G hloc S x i (hr.trans_le hri))))
      · have he : (fun ω : Set E => r ≤ i → i < j →
            k < (intrinsicSphere G (ω ∩ S) x i).ncard) = fun _ => True := by
          funext ω; simp [hri]
        rw [he]
        exact measurable_const
    exact (measurable_const.and (measurable_const.and
      ((measurableSet_intrinsicBall_eq G hloc S x (j-1) U).mem.and
      ((measurableSet_intrinsicBall_eq G hloc S x j W).mem.and
      ((measurableSet_le (measurable_intrinsicSphere_ncard G hloc S x j hj0) measurable_const).mem.and hfirst))))).setOf
  · have he : thinSphereCell G S x r k j U W = ∅ := by
      ext ω; simp only [thinSphereCell,Set.mem_ofPred_eq,Set.mem_empty_iff_false]
      simp [hrj]
    rw [he]
    exact MeasurableSet.empty

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ThinSphereStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_domainRadiusEvent [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V) (n : ℕ) :
    MeasurableSet (domainRadiusEvent G S x n) := by
  have hm : Measurable (fun ω : Set E => ω ∩ S) :=
    measurable_set_iff.mpr (fun e => (measurable_set_mem e).and measurable_const)
  exact (measurableSet_intrinsicRadiusEvent G hloc x n).preimage hm

theorem measurableSet_activeThinSphereCell [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V)
    (r k j : ℕ) (hr : 0 < r) (U W : Finset V) :
    MeasurableSet (activeThinSphereCell G S x r k j U W) :=
  (measurableSet_thinSphereCell G hloc S x r k j hr U W).inter
    (measurableSet_domainRadiusEvent G hloc S x r)

theorem activeThinSphereCell_pairwise (G : BondGraph V E) (S : Set E) (x : V) (r k : ℕ) :
    Pairwise (fun a b : ℕ × Finset V × Finset V =>
      Disjoint (activeThinSphereCell G S x r k a.1 a.2.1 a.2.2)
        (activeThinSphereCell G S x r k b.1 b.2.1 b.2.2)) := by
  intro a b hab
  exact (thinSphereCell_pairwise G S x r k hab).mono Set.inter_subset_left Set.inter_subset_left

theorem activeThinSphereCell_dependsOn (G : BondGraph V E) (S : Set E) (x : V)
    (r k j : ℕ) (hr : 0 < r) (U W : Finset V) :
    DependsOn (fun ω => ω ∈ activeThinSphereCell G S x r k j U W) (ballIncidentEdges G U) := by
  intro ω η hagree
  apply propext
  have hforward (ω η : Set E)
      (hωη : ∀ e ∈ ballIncidentEdges G U, (e ∈ ω) = (e ∈ η))
      (hω : ω ∈ activeThinSphereCell G S x r k j U W) :
      η ∈ activeThinSphereCell G S x r k j U W := by
    have hθη := ((thinSphereCell_dependsOn G S x r k j hr U W) hωη).to_iff.mp hω.1
    have hU := hω.1.2.2.1
    have hrj := hω.1.1
    have hballs := intrinsicBall_history_eq_of_incident_agreement G (ω ∩ S) (η ∩ S) x j (by
      intro e he
      rw [hU] at he
      exact and_congr (hωη e he).to_iff Iff.rfl)
    refine ⟨hθη,?_⟩
    have hR := hω.2
    change ω ∩ S ∈ intrinsicRadiusEvent G x r at hR
    change η ∩ S ∈ intrinsicRadiusEvent G x r
    rw [intrinsicRadiusEvent_iff_sphere,intrinsicSphere_eq_ball_sdiff G _ x r hr,
      hballs r hrj,hballs (r-1) ((Nat.sub_le r 1).trans hrj)] at hR
    rw [intrinsicRadiusEvent_iff_sphere,intrinsicSphere_eq_ball_sdiff G _ x r hr]
    exact hR
  exact ⟨hforward ω η hagree,hforward η ω (fun e he => (hagree e he).symm)⟩

theorem exists_activeThinSphereCell_of_small_cluster (G : BondGraph V E)
    (hloc : LocallyFinite G) (S ω : Set E) (x : V) (r k : ℕ)
    (hf : (cluster G (ω ∩ S) x).Finite)
    (hsmall : (cluster G (ω ∩ S) x).ncard < (r+1)*(k+1))
    (hR : ω ∈ domainRadiusEvent G S x r) :
    ∃ a : ℕ × Finset V × Finset V,
      ω ∈ activeThinSphereCell G S x r k a.1 a.2.1 a.2.2 := by
  obtain ⟨j,hj,hthin⟩ := exists_thin_intrinsicSphere G hloc (ω ∩ S) x r k hf hsmall
  have hex : ∃ j : ℕ, r ≤ j ∧ j ≤ 2*r ∧ (intrinsicSphere G (ω ∩ S) x j).ncard ≤ k :=
    ⟨j,(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,hthin⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  let hU := (finite_reachBall hloc x (j-1)).subset (intrinsicBall_subset_reachBall G (ω ∩ S) x (j-1))
  let hW := (finite_reachBall hloc x j).subset (intrinsicBall_subset_reachBall G (ω ∩ S) x j)
  refine ⟨(j,hU.toFinset,hW.toFinset),?_,hR⟩
  refine ⟨hj.1,hj.2.1,hU.coe_toFinset.symm,hW.coe_toFinset.symm,hj.2.2,?_⟩
  intro i hri hij
  by_contra hki
  have hi := Nat.find_min hex hij
  exact hi ⟨hri,(by omega),Nat.le_of_not_gt hki⟩

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ThinSphereProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem domainRadiusEvent_dependsOn (G : BondGraph V E) (S : Set E) (x : V) (n : ℕ) :
    DependsOn (fun ω => ω ∈ domainRadiusEvent G S x n) S := by
  intro ω η hagree
  have he : Set.inter ω S = Set.inter η S := by
    apply Set.ext
    intro e
    change (ω e ∧ e ∈ S) ↔ (η e ∧ e ∈ S)
    by_cases he : e ∈ S
    · simp only [he,and_true]
      exact (hagree e he).to_iff
    · simp only [he,and_false]
  change (Set.inter ω S ∈ intrinsicRadiusEvent G x n) =
    (Set.inter η S ∈ intrinsicRadiusEvent G x n)
  exact congrArg (fun B : Set E => B ∈ intrinsicRadiusEvent G x n) he

theorem activeThinSphereCell_fresh_factor [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (S : Set E) (x : V) (r k j : ℕ) (hr : 0 < r) (U W : Finset V) (z : V) :
    law p (activeThinSphereCell G S x r k j U W ∩
      domainRadiusEvent G (S \ ballIncidentEdges G U) z r) =
      law p (activeThinSphereCell G S x r k j U W) *
        law p (domainRadiusEvent G (S \ ballIncidentEdges G U) z r) := by
  unfold law
  rw [←CriticalPercolation.BernoulliProduct.law_const]
  apply CriticalPercolation.BernoulliProduct.measure_inter_of_separate_blocks
    (fun _ => p) (ballIncidentEdges G U) _ _
    (measurableSet_activeThinSphereCell G hloc S x r k j hr U W)
    (measurableSet_domainRadiusEvent G hloc _ z r)
    (activeThinSphereCell_dependsOn G S x r k j hr U W)
  intro ω η hagree
  apply domainRadiusEvent_dependsOn G (S \ ballIncidentEdges G U) z r
  intro e he
  exact hagree e he.2

theorem activeThinSphereCell_continuation (G : BondGraph V E) (S ω : Set E)
    (x : V) (r k j : ℕ) (hr : 0 < r) (U W : Finset V)
    (hcell : ω ∈ activeThinSphereCell G S x r k j U W)
    (hR : ω ∈ domainRadiusEvent G S x (3*r)) :
    ∃ z ∈ W \ U, ω ∈ domainRadiusEvent G (S \ ballIncidentEdges G U) z r := by
  have hj0 : 0 < j := hr.trans_le hcell.1.1
  have hj2 : j ≤ 2*r := hcell.1.2.1
  have hRjr : ω ∩ S ∈ intrinsicRadiusEvent G x (j+r) := by
    obtain ⟨y,hc,hd⟩ := hR
    exact ⟨y,hc,(by omega : j+r ≤ 3*r).trans hd⟩
  obtain ⟨z,hz,hfresh⟩ := intrinsic_radius_fresh_continuation G (ω ∩ S) x j r hj0 hRjr
  have hU := hcell.1.2.2.1
  have hW := hcell.1.2.2.2.1
  have hzWU : z ∈ W \ U := by
    rw [intrinsicSphere_eq_ball_sdiff G _ x j hj0,hU,hW] at hz
    exact_mod_cast hz
  refine ⟨z,hzWU,?_⟩
  change ω ∩ (S \ ballIncidentEdges G U) ∈ intrinsicRadiusEvent G z r
  rw [hU] at hfresh
  have he : (ω ∩ S) \ ballIncidentEdges G U = ω ∩ (S \ ballIncidentEdges G U) := by
    ext e; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
  rw [he] at hfresh
  exact hfresh

theorem activeThinSphereCell_frontier_card (G : BondGraph V E) (S ω : Set E)
    (x : V) (r k j : ℕ) (hr : 0 < r) (U W : Finset V)
    (hcell : ω ∈ activeThinSphereCell G S x r k j U W) : (W \ U).card ≤ k := by
  have hthin := hcell.1.2.2.2.2.1
  rw [intrinsicSphere_eq_ball_sdiff G _ x j (hr.trans_le hcell.1.1),
    hcell.1.2.2.1,hcell.1.2.2.2.1,←Finset.coe_sdiff,Set.ncard_coe_finset] at hthin
  exact hthin

theorem activeThinSphereCell_survival_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (S : Set E) (x : V) (r k j : ℕ) (hr : 0 < r) (U W : Finset V)
    (b : ℝ≥0∞) (hb : ∀ (I : Set E) z, law p (domainRadiusEvent G I z r) ≤ b) :
    law p (activeThinSphereCell G S x r k j U W ∩ domainRadiusEvent G S x (3*r)) ≤
      law p (activeThinSphereCell G S x r k j U W) * k * b := by
  let A := activeThinSphereCell G S x r k j U W
  by_cases hA : A.Nonempty
  · obtain ⟨ω,hω⟩ := hA
    have hcard := activeThinSphereCell_frontier_card G S ω x r k j hr U W hω
    have hsub : A ∩ domainRadiusEvent G S x (3*r) ⊆
        ⋃ z ∈ W \ U, A ∩ domainRadiusEvent G (S \ ballIncidentEdges G U) z r := by
      rintro η ⟨hη,hR⟩
      obtain ⟨z,hz,hfresh⟩ := activeThinSphereCell_continuation G S η x r k j hr U W hη hR
      exact Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,hη,hfresh⟩⟩
    calc
      _ ≤ law p (⋃ z ∈ W \ U, A ∩ domainRadiusEvent G (S \ ballIncidentEdges G U) z r) := measure_mono hsub
      _ ≤ ∑ z ∈ W \ U, law p (A ∩ domainRadiusEvent G (S \ ballIncidentEdges G U) z r) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ W \ U, law p A * b := by
        apply Finset.sum_le_sum
        intro z _
        rw [activeThinSphereCell_fresh_factor G hloc p S x r k j hr U W z]
        exact mul_le_mul' le_rfl (hb _ z)
      _ = law p A * (W \ U).card * b := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl (by exact_mod_cast hcard)) le_rfl
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    change law p (A ∩ _) ≤ law p A * _ * _
    rw [he]
    simp

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BallSnapshot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem ballSnapshotCell_dependsOn (G : BondGraph V E) (x : V)
    (j : ℕ) (U W : Finset V) :
    DependsOn (fun ω => ω ∈ ballSnapshotCell G x j U W) (ballIncidentEdges G U) := by
  intro ω η hagree
  apply propext
  have hforward (ω η : Set E)
      (hωη : ∀ e ∈ ballIncidentEdges G U, e ∈ ω ↔ e ∈ η)
      (hω : ω ∈ ballSnapshotCell G x j U W) : η ∈ ballSnapshotCell G x j U W := by
    have hballs := intrinsicBall_history_eq_of_incident_agreement G ω η x j (by
      intro e he
      rw [hω.1] at he
      exact hωη e he)
    exact ⟨(hballs (j-1) (Nat.sub_le j 1)).symm.trans hω.1,(hballs j le_rfl).symm.trans hω.2⟩
  exact ⟨hforward ω η (fun e he => (hagree e he).to_iff),
    hforward η ω (fun e he => (hagree e he).symm.to_iff)⟩

theorem measurableSet_ballSnapshotCell [Countable V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (x : V) (j : ℕ) (U W : Finset V) :
    MeasurableSet (ballSnapshotCell G x j U W) := by
  have hU := measurableSet_intrinsicBall_eq G hloc Set.univ x (j-1) U
  have hW := measurableSet_intrinsicBall_eq G hloc Set.univ x j W
  simpa only [ballSnapshotCell, Set.inter_univ, Set.ofPred_and] using hU.inter hW

theorem ballSnapshotCell_pairwise (G : BondGraph V E) (x : V) (j : ℕ) :
    Pairwise (fun a b : Finset V × Finset V =>
      Disjoint (ballSnapshotCell G x j a.1 a.2) (ballSnapshotCell G x j b.1 b.2)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro ω ha hb
  apply hab
  exact Prod.ext (Finset.coe_injective (ha.1.symm.trans hb.1))
    (Finset.coe_injective (ha.2.symm.trans hb.2))

theorem exists_ballSnapshotCell (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (j : ℕ) :
    ∃ a : Finset V × Finset V, ω ∈ ballSnapshotCell G x j a.1 a.2 := by
  let hU := (finite_reachBall hloc x (j-1)).subset (intrinsicBall_subset_reachBall G ω x (j-1))
  let hW := (finite_reachBall hloc x j).subset (intrinsicBall_subset_reachBall G ω x j)
  exact ⟨(hU.toFinset,hW.toFinset),hU.coe_toFinset.symm,hW.coe_toFinset.symm⟩

theorem ballSnapshotCell_fresh_connection_factor [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (x y z : V) (j : ℕ) (U W : Finset V) :
    law p (ballSnapshotCell G x j U W ∩
      {ω | Conn G (ω \ ballIncidentEdges G U) z y}) =
      law p (ballSnapshotCell G x j U W) *
        law p {ω | Conn G (ω \ ballIncidentEdges G U) z y} := by
  have hm : Measurable (fun ω : Set E => ω \ ballIncidentEdges G U) :=
    measurable_set_iff.mpr (fun e => (measurable_set_mem e).and measurable_const)
  unfold law
  rw [←CriticalPercolation.BernoulliProduct.law_const]
  apply CriticalPercolation.BernoulliProduct.measure_inter_of_separate_blocks
    (fun _ => p) (ballIncidentEdges G U) _ _
    (measurableSet_ballSnapshotCell G hloc x j U W)
    ((measurableSet_conn G z y).preimage hm)
    (ballSnapshotCell_dependsOn G x j U W)
  intro ω η hagree
  have he : Set.diff ω (ballIncidentEdges G U) = Set.diff η (ballIncidentEdges G U) := by
    apply Set.ext
    intro e
    change (ω e ∧ e ∉ ballIncidentEdges G U) ↔ (η e ∧ e ∉ ballIncidentEdges G U)
    by_cases hi : e ∈ ballIncidentEdges G U
    · simp only [hi,not_true_eq_false,and_false]
    · simp only [hi,not_false_eq_true,and_true]
      exact (hagree e hi).to_iff
  change (Conn G (Set.diff ω (ballIncidentEdges G U)) z y) =
    (Conn G (Set.diff η (ballIncidentEdges G U)) z y)
  rw [he]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_intrinsicSphereEvent (G : BondGraph V E) (hloc : LocallyFinite G)
    (x z : V) (j : ℕ) (hj : 0 < j) : MeasurableSet (intrinsicSphereEvent G x z j) := by
  have he : intrinsicSphereEvent G x z j =
      {ω | z ∈ intrinsicBall G ω x j} \ {ω | z ∈ intrinsicBall G ω x (j-1)} := by
    ext ω
    exact Set.ext_iff.mp (intrinsicSphere_eq_ball_sdiff G ω x j hj) z
  rw [he]
  exact (measurableSet_mem_intrinsicBall G hloc x z j).diff
    (measurableSet_mem_intrinsicBall G hloc x z (j-1))

theorem snapshotFrontierCell_iUnion (G : BondGraph V E) (hloc : LocallyFinite G)
    (x z : V) (j : ℕ) (hj : 0 < j) :
    (⋃ a : Finset V × Finset V, snapshotFrontierCell G x z j a) = intrinsicSphereEvent G x z j := by
  ext ω
  constructor
  · intro h
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp h
    by_cases hz : z ∈ a.2 \ a.1
    · rw [snapshotFrontierCell,ite_eq_left hz] at ha
      change z ∈ intrinsicSphere G ω x j
      rw [intrinsicSphere_eq_ball_sdiff G _ x j hj,ha.1,ha.2]
      exact_mod_cast hz
    · simp only [snapshotFrontierCell,ite_eq_right hz,Set.mem_empty_iff_false] at ha
  · intro hz
    obtain ⟨a,ha⟩ := exists_ballSnapshotCell G hloc ω x j
    have hz' : z ∈ a.2 \ a.1 := by
      change z ∈ intrinsicSphere G ω x j at hz
      rw [intrinsicSphere_eq_ball_sdiff G _ x j hj,ha.1,ha.2] at hz
      exact_mod_cast hz
    exact Set.mem_iUnion.mpr ⟨a,by simpa only [snapshotFrontierCell,ite_eq_left hz'] using ha⟩

theorem snapshotFrontierCell_pairwise (G : BondGraph V E) (x z : V) (j : ℕ) :
    Pairwise (fun a b : Finset V × Finset V =>
      Disjoint (snapshotFrontierCell G x z j a) (snapshotFrontierCell G x z j b)) := by
  intro a b hab
  have ha : snapshotFrontierCell G x z j a ⊆ ballSnapshotCell G x j a.1 a.2 := by
    unfold snapshotFrontierCell; split <;> simp
  have hb : snapshotFrontierCell G x z j b ⊆ ballSnapshotCell G x j b.1 b.2 := by
    unfold snapshotFrontierCell; split <;> simp
  exact (ballSnapshotCell_pairwise G x j hab).mono ha hb

theorem measurableSet_snapshotFrontierCell [Countable V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (x z : V) (j : ℕ) (a : Finset V × Finset V) :
    MeasurableSet (snapshotFrontierCell G x z j a) := by
  unfold snapshotFrontierCell
  split
  · exact measurableSet_ballSnapshotCell G hloc x j a.1 a.2
  · exact MeasurableSet.empty

theorem longConnection_sphere_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (x y : V) (n j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
    law p (longConnectionEvent G x y n) ≤
      ∑' z, law p (intrinsicSphereEvent G x z j) * law p {ω | Conn G ω z y} := by
  let F := fun (a : Finset V × Finset V) (z : V) =>
    snapshotFrontierCell G x z j a ∩ {ω | Conn G (ω \ ballIncidentEdges G a.1) z y}
  have hcover : longConnectionEvent G x y n ⊆ ⋃ a, ⋃ z, F a z := by
    rintro ω ⟨hc,hd⟩
    obtain ⟨a,ha⟩ := exists_ballSnapshotCell G hloc ω x j
    obtain ⟨z,hz,hfresh,_⟩ := intrinsic_long_connection_fresh G ω x y j 0 hj hc
      (by simpa only [Nat.add_zero] using hjn.trans hd)
    have hz' : z ∈ a.2 \ a.1 := by
      rw [intrinsicSphere_eq_ball_sdiff G _ x j hj,ha.1,ha.2] at hz
      exact_mod_cast hz
    apply Set.mem_iUnion.mpr
    refine ⟨a,Set.mem_iUnion.mpr ⟨z,?_,?_⟩⟩
    · simpa only [snapshotFrontierCell,ite_eq_left hz'] using ha
    · rw [ha.1] at hfresh
      exact hfresh
  have hF (a : Finset V × Finset V) (z : V) :
      law p (F a z) ≤ law p (snapshotFrontierCell G x z j a) * law p {ω | Conn G ω z y} := by
    by_cases hz : z ∈ a.2 \ a.1
    · dsimp only [F]
      rw [snapshotFrontierCell,ite_eq_left hz,ballSnapshotCell_fresh_connection_factor G hloc p x y z j a.1 a.2]
      apply mul_le_mul' le_rfl
      apply measure_mono
      intro ω hω
      exact conn_mono G Set.sdiff_subset hω
    · simp only [F,snapshotFrontierCell,ite_eq_right hz,Set.empty_inter,measure_empty,zero_mul,le_refl]
  calc
    _ ≤ law p (⋃ a, ⋃ z, F a z) := measure_mono hcover
    _ ≤ ∑' a, ∑' z, law p (F a z) :=
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun a => measure_iUnion_le (F a)))
    _ ≤ ∑' a, ∑' z, law p (snapshotFrontierCell G x z j a) * law p {ω | Conn G ω z y} :=
      ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (hF a))
    _ = ∑' z, (∑' a, law p (snapshotFrontierCell G x z j a)) * law p {ω | Conn G ω z y} := by
      rw [ENNReal.tsum_comm]
      simp only [ENNReal.tsum_mul_right]
    _ = _ := by
      apply tsum_congr
      intro z
      rw [←measure_iUnion (snapshotFrontierCell_pairwise G x z j)
        (measurableSet_snapshotFrontierCell G hloc x z j),snapshotFrontierCell_iUnion G hloc x z j hj]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicConnectionAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsic_sphere_interval_sum_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x z : V) (m n : ℕ) :
    (∑ j ∈ Finset.Icc (m+1) n, law p (intrinsicSphereEvent G x z j)) ≤
      law p (longConnectionEvent G x z m) := by
  have hdisj : (↑(Finset.Icc (m+1) n) : Set ℕ).PairwiseDisjoint (intrinsicSphereEvent G x z) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro ω ⟨_,hi⟩ ⟨_,hj⟩
    exact hij (hi.symm.trans hj)
  rw [←measure_biUnion_finset hdisj (fun j hj => measurableSet_intrinsicSphereEvent G hloc x z j
    (by have h := (Finset.mem_Icc.mp hj).1; omega))]
  apply measure_mono
  intro ω hω
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hji,hz⟩ := Set.mem_iUnion.mp hj
  exact ⟨hz.1,((Nat.le_succ m).trans (Finset.mem_Icc.mp hji).1).trans_eq hz.2.symm⟩

theorem longConnection_interval_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (x y : V) (m n : ℕ) :
    (n-m : ℕ) * law p (longConnectionEvent G x y n) ≤
      ∑' z, law p (longConnectionEvent G x z m) * law p {ω | Conn G ω z y} := by
  have havg := Finset.sum_le_sum (s := Finset.Icc (m+1) n) (fun j hj => longConnection_sphere_bound G hloc p x y n j
    (by have h := (Finset.mem_Icc.mp hj).1; omega) (Finset.mem_Icc.mp hj).2)
  have hcard : (Finset.Icc (m+1) n).card = n-m := by rw [Nat.card_Icc]; omega
  calc
    _ = ∑ j ∈ Finset.Icc (m+1) n, law p (longConnectionEvent G x y n) := by
      simp only [Finset.sum_const,nsmul_eq_mul,hcard]
    _ ≤ ∑ j ∈ Finset.Icc (m+1) n,
        ∑' z, law p (intrinsicSphereEvent G x z j) * law p {ω | Conn G ω z y} := havg
    _ = ∑' z, ∑ j ∈ Finset.Icc (m+1) n,
        law p (intrinsicSphereEvent G x z j) * law p {ω | Conn G ω z y} :=
      (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
    _ = ∑' z, (∑ j ∈ Finset.Icc (m+1) n, law p (intrinsicSphereEvent G x z j)) *
        law p {ω | Conn G ω z y} := by simp only [Finset.sum_mul]
    _ ≤ _ := ENNReal.tsum_le_tsum (fun z => mul_le_mul'
      (intrinsic_sphere_interval_sum_le G hloc p x z m n) le_rfl)

theorem longConnection_power_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (M k : ℕ) (x y : V) :
    (M : ℝ≥0∞)^k * law p (longConnectionEvent G x y (k*M)) ≤
      ennMatrixCoeff (T^(k+1)) x y := by
  have hpos := hT.positiveRealMatrix G p T
  induction k generalizing x y with
  | zero =>
    rw [pow_zero,one_mul,Nat.zero_mul,pow_one,hT.ennMatrixCoeff G p T]
    apply measure_mono
    intro ω hω
    exact hω.1
  | succ k ih =>
    have hrec := longConnection_interval_bound G hloc p x y (k*M) ((k+1)*M)
    have hsub : (k+1)*M-k*M = M := by rw [Nat.add_mul]; omega
    rw [hsub] at hrec
    calc
      _ = (M : ℝ≥0∞)^k * (M * law p (longConnectionEvent G x y ((k+1)*M))) := by rw [pow_succ,mul_assoc]
      _ ≤ (M : ℝ≥0∞)^k * ∑' z, law p (longConnectionEvent G x z (k*M)) * law p {ω | Conn G ω z y} :=
        mul_le_mul' le_rfl hrec
      _ = ∑' z, ((M : ℝ≥0∞)^k * law p (longConnectionEvent G x z (k*M))) * law p {ω | Conn G ω z y} := by
        rw [←ENNReal.tsum_mul_left]
        simp only [mul_assoc]
      _ ≤ ∑' z, ennMatrixCoeff (T^(k+1)) x z * ennMatrixCoeff T z y := by
        apply ENNReal.tsum_le_tsum
        intro z
        rw [hT.ennMatrixCoeff G p T]
        exact mul_le_mul' (ih x z) le_rfl
      _ = _ := by
        rw [←ennMatrixCoeff_mul (hpos.pow (k+1)) hpos,←pow_succ]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicBallisticity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem longConnectionEvent_antitone (G : BondGraph V E) (x y : V)
    {m n : ℕ} (hmn : m ≤ n) : longConnectionEvent G x y n ⊆ longConnectionEvent G x y m := by
  rintro ω ⟨hc,hd⟩
  exact ⟨hc,hmn.trans hd⟩

theorem longConnection_block_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (M k n : ℕ) (hM : 0 < M) (x y : V) (hd : k*M ≤ n) :
    (law p).real (longConnectionEvent G x y n) ≤ ‖T‖ * (‖T‖ / M)^k := by
  have hpow := longConnection_power_bound G hloc p T hT M k x y
  have hreal : (M : ℝ)^k * (law p).real (longConnectionEvent G x y (k*M)) ≤
      (matrixCoeff (T^(k+1)) x y).re := by
    change (M : ℝ)^k * (law p (longConnectionEvent G x y (k*M))).toReal ≤ _
    have hh := ENNReal.toReal_mono (by unfold ennMatrixCoeff; exact ENNReal.ofReal_ne_top) hpow
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
      ennMatrixCoeff,ENNReal.toReal_ofReal ((hT.positiveRealMatrix G p T).pow (k+1) x y).2] using hh
  have hcoeff : (matrixCoeff (T ^ (k + 1)) x y).re ≤ ‖T‖ ^ (k + 1) := by
    apply (Complex.re_le_norm _).trans
    have hc : ‖matrixCoeff (T ^ (k + 1)) x y‖ ≤ ‖T ^ (k + 1)‖ := by
      change ‖(T ^ (k + 1)) (lp.single 2 y (1 : ℂ)) x‖ ≤ _
      apply (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        ((T ^ (k + 1)) (lp.single 2 y (1 : ℂ))) x).trans
      simpa only [lp.norm_single (by norm_num : 0 < (2 : ENNReal)), norm_one, mul_one] using
        (T ^ (k + 1)).le_opNorm (lp.single 2 y (1 : ℂ))
    exact hc.trans (norm_pow_le' T (Nat.zero_lt_succ k))
  have hc : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ (law p).real (longConnectionEvent G x y (k*M)) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (longConnectionEvent_antitone G x y hd))
    _ ≤ ‖T‖^(k+1) / (M : ℝ)^k :=
      (le_div_iff₀ (pow_pos hc k)).mpr (by simpa only [mul_comm] using hreal.trans hcoeff)
    _ = _ := by rw [div_pow,pow_succ]; ring

theorem longConnection_exponential_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (x y : V) (n : ℕ) :
    (law p).real (longConnectionEvent G x y n) ≤ 2 * ‖T‖ *
      Real.exp (-(Real.log 2 / (3 * ‖T‖)) * n) := by
  have hM : 1 ≤ ‖T‖ := hT.norm_one_le G p T
  have hMp : 0 < ‖T‖ := lt_of_lt_of_le zero_lt_one hM
  let m : ℕ := ⌈2 * ‖T‖⌉₊
  have hml : 2 * ‖T‖ ≤ (m : ℝ) := Nat.le_ceil _
  have hmu : (m : ℝ) ≤ 3 * ‖T‖ := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * ‖T‖ by positivity)
    dsimp [m]
    linarith
  have hmp : 0 < m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hml
    exact_mod_cast this
  let k := n / m
  have hk : k * m ≤ n := Nat.div_mul_le_self _ _
  have hxy : n < (k + 1) * m := by
    simpa only [k, Nat.mul_comm] using Nat.lt_mul_div_succ (n) hmp
  have hr : ‖T‖ / m ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < m)).mpr
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ‖T‖ / m) hr k
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : (n : ℝ) ≤ ((k : ℝ) + 1) * (3 * ‖T‖) := by
    have h1 : (n : ℝ) ≤ ((k : ℝ) + 1) * m := by
      exact_mod_cast hxy.le
    exact h1.trans (mul_le_mul_of_nonneg_left hmu (by positivity))
  have hexponent : -(Real.log 2) * k ≤
      Real.log 2 - (Real.log 2 / (3 * ‖T‖)) * n := by
    have hdiv : (n : ℝ) / (3 * ‖T‖) ≤ (k : ℝ) + 1 :=
      (div_le_iff₀ (by positivity)).mpr hcast
    have hh := mul_le_mul_of_nonneg_left hdiv hlog.le
    nlinarith [show (Real.log 2 / (3 * ‖T‖)) * n =
      Real.log 2 * ((n : ℝ) / (3 * ‖T‖)) by ring]
  have hhalf : (1 / 2 : ℝ) ^ k = Real.exp (-(Real.log 2) * k) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  calc
    _ ≤ ‖T‖ * (‖T‖ / m) ^ k :=
      longConnection_block_bound G hloc p T hT m k n hmp x y hk
    _ ≤ ‖T‖ * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = ‖T‖ * Real.exp (-(Real.log 2) * k) := by rw [hhalf]
    _ ≤ ‖T‖ * Real.exp (Real.log 2 -
        (Real.log 2 / (3 * ‖T‖)) * n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (norm_nonneg _)
    _ = _ := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        neg_mul, Real.exp_neg, div_eq_mul_inv]
      ring

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_VolumeLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem critical_volume_lower_of_upper [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc1 : (pc G : ℝ) < 1)
    (C : ℝ) (hC : 0 < C)
    (hvol : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n)
    (x : V) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 0 < n → a / Real.sqrt n ≤ criticalTail G (volumeEvent G) x n := by
  obtain ⟨c,hc,hθ⟩ := percolationProbability_linear_lower G hconn hloc hqt x
  obtain ⟨d,_,hdeg⟩ := exists_degree_bound G hqt
  have hpc0 : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  let D : ℝ := (pc G : ℝ) * (1-pc G)/2
  have hD : 0 < D := by dsimp [D]; positivity
  let L : ℝ := 2 + 2*(d : ℝ)/D
  have hL : 0 < L := by dsimp [L]; positivity
  let b : ℝ := min (1/2) (min ((1-pc G)/2) (c/(8*L*C)))
  have hb : 0 < b := lt_min (by norm_num)
    (lt_min (by positivity) (div_pos hc (by positivity)))
  have hbhalf : b ≤ 1/2 := min_le_left _ _
  have hbgap : b ≤ (1-pc G)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hbsmall : b ≤ c/(8*L*C) := (min_le_right _ _).trans (min_le_right _ _)
  have hbc : 8*L*C*b ≤ c := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*L*C)).mp hbsmall
    nlinarith
  refine ⟨c*b/(4*L),by positivity,fun n hn => ?_⟩
  let s : ℝ := Real.sqrt n
  have hs1 : 1 ≤ s := by
    dsimp [s]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hs : 0 < s := zero_lt_one.trans_le hs1
  let δ : ℝ := b/s
  have hδ : 0 < δ := div_pos hb hs
  have hδb : δ ≤ b := div_le_self hb.le hs1
  have hδhalf : δ ≤ 1/2 := hδb.trans hbhalf
  have hδgap : δ ≤ (1-pc G)/2 := hδb.trans hbgap
  let q : unitInterval := ⟨(pc G : ℝ)+δ,⟨by positivity,by linarith⟩⟩
  have hq : pc G < q := by change (pc G : ℝ) < pc G+δ; linarith
  have hq1 : (q : ℝ) < 1 := by change (pc G : ℝ)+δ < 1; linarith
  have hq0 : 0 < (q : ℝ) := hpc0.trans hq
  have hden : D ≤ (q : ℝ)*(1-q) := by
    have ht : (1-(pc G : ℝ))/2 ≤ 1-(q : ℝ) := by dsimp [q]; linarith
    have hm := mul_le_mul (show (pc G : ℝ) ≤ q from hq.le) ht
      (by positivity : 0 ≤ (1-(pc G : ℝ))/2) hq0.le
    dsimp [D]
    nlinarith
  let h : unitInterval := ⟨δ^2,⟨sq_nonneg _,by nlinarith⟩⟩
  have hh : (h : ℝ) ∈ Set.Ioo 0 1 := ⟨sq_pos_of_pos hδ,by dsimp [h]; nlinarith⟩
  have hmark (Q : Finset E) : markedConnectionPolynomial G Q x h (pc G) ≤
      (h : ℝ)*(2*C*s) + criticalTail G (volumeEvent G) x n := by
    have hsum : (∑ i ∈ Finset.range n, finiteClusterTail G Q x (i+1) (pc G)) ≤ 2*C*s := by
      calc
        _ ≤ ∑ i ∈ Finset.range n, C / Real.sqrt (i+1 : ℕ) :=
          Finset.sum_le_sum (fun i _ => (finiteClusterTail_le_criticalTail G Q x (i+1) (pc G) le_rfl).trans
            (hvol x (i+1) (by omega)))
        _ = C * ∑ i ∈ Finset.range n, 1 / Real.sqrt (i+1 : ℕ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ C*(2*s) := mul_le_mul_of_nonneg_left (sum_inverse_sqrt_le n) hC.le
        _ = _ := by ring
    exact (markedConnection_le_truncated_tails G Q x (pc G) h n).trans
      (add_le_add (mul_le_mul_of_nonneg_left hsum h.2.1)
        (finiteClusterTail_le_criticalTail G Q x n (pc G) le_rfl))
  have hghost (Q : Finset E) : markedConnectionPolynomial G Q x h q ≤
      L*((h : ℝ)*(2*C*s) + criticalTail G (volumeEvent G) x n) := by
    have ht := markedConnection_entropy_uniform G Q x (pc G) q h ⟨hpc0,hpc1⟩
      ⟨hq0,hq1⟩ hh d (fun z => (incident_filter_card_le_degree G hloc Q z).trans (hdeg z))
      D hD hden (by change ((pc G : ℝ)-((pc G : ℝ)+δ))^2 ≤ δ^2; nlinarith)
    exact ht.trans (mul_le_mul_of_nonneg_left (hmark Q) hL.le)
  have hupper := percolationProbability_le_of_marked_bounds G x q h hh.1 _ hghost
  have hlower := hθ q hq hq1
  have hδs : δ*s = b := div_mul_cancel₀ b hs.ne'
  have hbound : c*δ ≤ 2*(L*(δ^2*(2*C*s) + criticalTail G (volumeEvent G) x n)) := by
    dsimp only [q] at hlower
    dsimp only [h] at hupper
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hs.le
  have halg : (2*(L*(δ^2*(2*C*s) + criticalTail G (volumeEvent G) x n)))*s =
      4*L*C*b^2 + 2*L*(criticalTail G (volumeEvent G) x n*s) := by
    rw [←hδs]
    ring
  rw [halg,mul_assoc c δ s,hδs] at hm
  have hsmall : 4*L*C*b^2 ≤ c*b/2 := by
    have ht := mul_le_mul_of_nonneg_right hbc hb.le
    nlinarith
  apply (div_le_iff₀ hs).mpr
  apply (div_le_iff₀ (by positivity : 0 < 4*L)).mpr
  nlinarith

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicRadiusLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_eq_intrinsicBall_of_not_radius (G : BondGraph V E)
    (ω : Set E) (x : V) (r : ℕ) (hr : ω ∉ intrinsicRadiusEvent G x r) :
    cluster G ω x = intrinsicBall G ω x r := by
  apply Set.Subset.antisymm
  · intro y hy
    apply (intrinsicBall_iff_distance_le G ω x y r hy).mpr
    have hn : ¬ r ≤ (openSimpleGraph G ω).dist x y := fun hd => hr ⟨y,hy,hd⟩
    omega
  · rintro y ⟨l,hl,_,ho⟩
    exact hl.conn ho

theorem volume_le_radius_add_intrinsicBallMoment [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (x : V) (r N : ℕ) (hN : 0 < N) :
    (law p (volumeEvent G x N)).toReal ≤
      (law p (intrinsicRadiusEvent G x r)).toReal +
        intrinsicBallMoment G hloc Set.univ x r p / N := by
  let A : Set (Set E) := {ω | (N : ℝ) ≤ (intrinsicBall G ω x r).ncard}
  have hsub : volumeEvent G x N ⊆ intrinsicRadiusEvent G x r ∪ A := by
    intro ω hω
    by_cases hr : ω ∈ intrinsicRadiusEvent G x r
    · exact Or.inl hr
    · apply Or.inr
      have hf := (finite_reachBall hloc x r).subset (intrinsicBall_subset_reachBall G ω x r)
      have he := cluster_eq_intrinsicBall_of_not_radius G ω x r hr
      change (N : ℕ∞) ≤ (cluster G ω x).encard at hω
      rw [he,←hf.cast_ncard_eq] at hω
      have hn : N ≤ (intrinsicBall G ω x r).ncard := by exact_mod_cast hω
      change (N : ℝ) ≤ (intrinsicBall G ω x r).ncard
      exact_mod_cast hn
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := law p) (f := fun ω => ((intrinsicBall G ω x r).ncard : ℝ))
    (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))
    (by simpa only [Set.inter_univ] using integrable_intrinsicBall_ncard G hloc Set.univ x r p) (N : ℝ)
  have he : (∫ ω, ((intrinsicBall G ω x r).ncard : ℝ) ∂law p) =
      intrinsicBallMoment G hloc Set.univ x r p := by
    simpa only [Set.inter_univ] using integral_intrinsicBall_ncard_eq G hloc Set.univ x r p
  rw [he] at hm
  have hmark : (law p A).toReal ≤ intrinsicBallMoment G hloc Set.univ x r p / N := by
    apply (le_div_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mpr
    change (N : ℝ) * (law p A).toReal ≤ _ at hm
    simpa only [mul_comm] using hm
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add le_rfl hmark))

theorem critical_intrinsic_radius_lower_of_volume_and_ball [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V)
    (a C : ℝ) (ha : 0 < a) (_hC : 0 < C)
    (hvol : ∀ N : ℕ, 0 < N → a / Real.sqrt N ≤ criticalTail G (volumeEvent G) x N)
    (hball : ∀ r : ℕ, 0 < r → intrinsicBallMoment G hloc Set.univ x r (pc G) ≤ C * r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 0 < r →
      c / r ≤ criticalTail G (intrinsicRadiusEvent G) x r := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (2*C/a))
  have hm1 : 1 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast (zero_lt_one.trans hm1)
  have hma : 2*C < a*m := by
    have hh := (div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hm)
    nlinarith
  refine ⟨a/(2*m),by positivity,fun r hr => ?_⟩
  let N := (m*r)^2
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hN : 0 < N := by dsimp [N]; positivity
  have hNr : (N : ℝ) = ((m : ℝ)*r)^2 := by dsimp [N]; push_cast; rfl
  have hsqrt : Real.sqrt N = (m : ℝ)*r := by
    rw [hNr,Real.sqrt_sq (by positivity)]
  have hb := volume_le_radius_add_intrinsicBallMoment G hloc (pc G) x r N hN
  have hv := hvol N hN
  have hballs := hball r hr
  change a / Real.sqrt N ≤ (law (pc G) (volumeEvent G x N)).toReal at hv
  have hbound : a / ((m : ℝ)*r) ≤ criticalTail G (intrinsicRadiusEvent G) x r + C*r / N := by
    rw [hsqrt] at hv
    exact hv.trans (hb.trans (add_le_add le_rfl
      (div_le_div_of_nonneg_right hballs (Nat.cast_nonneg N))))
  rw [hNr] at hbound
  have hmR : 0 < (m : ℝ) := by positivity
  have hmult := (div_le_iff₀ (mul_pos hmR hr0)).mp hbound
  have hcancel : (criticalTail G (intrinsicRadiusEvent G) x r + C*r / ((m : ℝ)*r)^2) * ((m : ℝ)*r) =
      criticalTail G (intrinsicRadiusEvent G) x r * ((m : ℝ)*r) + C/m := by
    field_simp
  rw [hcancel] at hmult
  have hCm : C/m ≤ a/2 := by apply (div_le_iff₀ hmR).mpr; nlinarith
  apply (div_le_iff₀ hr0).mpr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*m)).mpr
  nlinarith

theorem critical_intrinsic_radius_lower_of_operator [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) (x : V) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 0 < r →
      c / r ≤ criticalTail G (intrinsicRadiusEvent G) x r := by
  obtain ⟨A,hA,hχ⟩ := susceptibility_upper_of_critical_operator_bs G hconn hloc hqt hh T hT
  obtain ⟨C,hC,hball⟩ := critical_intrinsicBallMoment_linear G hloc hqt A hA hχ
  obtain ⟨B,hB,hvol⟩ := critical_volume_upper_of_operator_bs G hconn hloc hqt hh hpc1 T hT
  obtain ⟨a,ha,hlo⟩ := critical_volume_lower_of_upper G hconn hloc hqt hpc1 B hB hvol x
  exact critical_intrinsic_radius_lower_of_volume_and_ball G hloc x a C ha hC hlo (hball Set.univ x)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ThinSphereRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem domain_cluster_subset (G : BondGraph V E) (S ω : Set E) (x : V) :
    cluster G (ω ∩ S) x ⊆ cluster G ω x :=
  fun _ h => conn_mono G Set.inter_subset_left h

theorem radius_thin_sphere_recurrence [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (r k : ℕ) (hr : 0 < r) (b : ℝ≥0∞)
    (hb : ∀ (I : Set E) z, law p (domainRadiusEvent G I z r) ≤ b)
    (S : Set E) (x : V) :
    law p (domainRadiusEvent G S x (3*r)) ≤
      law p (volumeEvent G x ((r+1)*(k+1))) + k * b^2 := by
  let A : (ℕ × Finset V × Finset V) → Set (Set E) := fun a =>
    activeThinSphereCell G S x r k a.1 a.2.1 a.2.2
  let R := domainRadiusEvent G S x (3*r)
  have hmA (a) : MeasurableSet (A a) :=
    measurableSet_activeThinSphereCell G hloc S x r k a.1 hr a.2.1 a.2.2
  have hdisj : Pairwise (fun a c => Disjoint (A a) (A c)) := activeThinSphereCell_pairwise G S x r k
  have hsub : R ≤ᵐ[law p] (volumeEvent G x ((r+1)*(k+1)) ∪ ⋃ a, A a ∩ R : Set (Set E)) := by
    filter_upwards [hfin x] with ω hω
    intro hR
    by_cases hv : ω ∈ volumeEvent G x ((r+1)*(k+1))
    · exact Or.inl hv
    · have hsmallG : (cluster G ω x).ncard < (r+1)*(k+1) := by
        change ¬ (((r+1)*(k+1) : ℕ) : ℕ∞) ≤ (cluster G ω x).encard at hv
        rw [←hω.cast_ncard_eq] at hv
        exact_mod_cast lt_of_not_ge hv
      have hdomain := domain_cluster_subset G S ω x
      have hf := hω.subset hdomain
      have hsmall : (cluster G (ω ∩ S) x).ncard < (r+1)*(k+1) :=
        (Set.ncard_le_ncard hdomain hω).trans_lt hsmallG
      have hRr : ω ∈ domainRadiusEvent G S x r := by
        obtain ⟨y,hc,hd⟩ := hR
        exact ⟨y,hc,(by omega : r ≤ 3*r).trans hd⟩
      obtain ⟨a,ha⟩ := exists_activeThinSphereCell_of_small_cluster G hloc S ω x r k hf hsmall hRr
      exact Or.inr (Set.mem_iUnion.mpr ⟨a,ha,hR⟩)
  have hsumA : (∑' a, law p (A a)) ≤ b := by
    rw [←measure_iUnion hdisj hmA]
    apply (measure_mono (show (⋃ a, A a) ⊆ domainRadiusEvent G S x r from ?_)).trans (hb S x)
    intro ω hω
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hω
    exact ha.2
  have hsum : (∑' a, law p (A a ∩ R)) ≤ k * b^2 := by
    calc
      _ ≤ ∑' a, law p (A a) * k * b := ENNReal.tsum_le_tsum (fun a =>
        activeThinSphereCell_survival_bound G hloc p S x r k a.1 hr a.2.1 a.2.2 b hb)
      _ = (∑' a, law p (A a)) * k * b := by rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_right]
      _ ≤ b * k * b := mul_le_mul' (mul_le_mul' hsumA le_rfl) le_rfl
      _ = _ := by ring
  exact (measure_mono_ae hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl ((measure_iUnion_le (fun a => A a ∩ R)).trans hsum)))

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicRadiusUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem thin_sphere_volume_scale (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (hlarge : 1000*C^2 ≤ A) (r : ℕ) (hr : 0 < r) :
    C / Real.sqrt ((r+1)*(Nat.floor ((r : ℝ)/(10*A))+1) : ℕ) ≤ A/(10*r) := by
  let k := Nat.floor ((r : ℝ)/(10*A))
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hk := (Nat.lt_floor_add_one ((r : ℝ)/(10*A))).le
  have hscale : (r : ℝ)^2/(10*A) ≤ ((r+1)*(k+1) : ℕ) := by
    push_cast
    calc
      _ = (r : ℝ) * ((r : ℝ)/(10*A)) := by ring
      _ ≤ (r : ℝ) * (k+1) := mul_le_mul_of_nonneg_left hk hr0.le
      _ ≤ _ := by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hs : 0 < Real.sqrt (10*A) := Real.sqrt_pos.mpr (by positivity)
  have hsN : (r : ℝ) / Real.sqrt (10*A) ≤ Real.sqrt ((r+1)*(k+1) : ℕ) := by
    have hh := Real.sqrt_le_sqrt hscale
    rw [Real.sqrt_div (sq_nonneg (r : ℝ)) (10*A),Real.sqrt_sq hr0.le] at hh
    exact hh
  have hcoeff : C * Real.sqrt (10*A) ≤ A/10 := by
    have hm := mul_le_mul_of_nonneg_right hlarge hA.le
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      (C * Real.sqrt (10*A))^2 = C^2*(10*A) := by rw [mul_pow,Real.sq_sqrt (by positivity)]
      _ ≤ (A/10)^2 := by nlinarith
  calc
    _ ≤ C / ((r : ℝ)/Real.sqrt (10*A)) :=
      div_le_div_of_nonneg_left hC.le (div_pos hr0 hs) hsN
    _ = (C*Real.sqrt (10*A)) / r := by field_simp
    _ ≤ (A/10)/r := div_le_div_of_nonneg_right hcoeff hr0.le
    _ = _ := by ring

theorem intrinsic_radius_upper_of_volume [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (C : ℝ) (hC : 0 < C)
    (hvol : ∀ (x : V) (N : ℕ), 0 < N → (law p (volumeEvent G x N)).toReal ≤ C/Real.sqrt N) :
    ∃ A : ℝ, 0 < A ∧ ∀ (S : Set E) x (n : ℕ), 0 < n →
      (law p (domainRadiusEvent G S x n)).toReal ≤ A/n := by
  let A := max 2 (1000*C^2)
  have hA2 : 2 ≤ A := le_max_left _ _
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA2
  have hlarge : 1000*C^2 ≤ A := le_max_right _ _
  refine ⟨A,hA,?_⟩
  suffices H : ∀ n : ℕ, ∀ (S : Set E) x, 0 < n →
      (law p (domainRadiusEvent G S x n)).toReal ≤ A/n from fun S x n hn => H n S x hn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S x hn
    by_cases hn3 : n < 3
    · apply measureReal_le_one.trans
      apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
      simpa only [one_mul] using hn2.trans hA2
    · let r := n/3
      have hr : 0 < r := Nat.div_pos (by omega) (by norm_num)
      have hrn : r < n := Nat.div_lt_self hn (by norm_num)
      have h3r : 3*r ≤ n := Nat.mul_div_le n 3
      have hn5 : n ≤ 5*r := by have hh := Nat.mod_lt n (by norm_num : 0 < 3); omega
      have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
      let k := Nat.floor ((r : ℝ)/(10*A))
      let b : ℝ≥0∞ := ENNReal.ofReal (A/r)
      have hb (I : Set E) (z : V) : law p (domainRadiusEvent G I z r) ≤ b := by
        rw [←ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal (ih r hrn I z hr)
      have hrec := radius_thin_sphere_recurrence G hloc p hfin r k hr b hb S x
      have hrecR := ENNReal.toReal_mono
        (show law p (volumeEvent G x ((r+1)*(k+1))) + k*b^2 ≠ ⊤ by finiteness) hrec
      dsimp only [b] at hrecR
      rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity)] at hrecR
      have hN : 0 < (r+1)*(k+1) := by positivity
      have hV : (law p (volumeEvent G x ((r+1)*(k+1)))).toReal ≤ A/(10*r) :=
        (hvol x _ hN).trans (thin_sphere_volume_scale C A hC hA hlarge r hr)
      have hk : (k : ℝ) ≤ (r : ℝ)/(10*A) := Nat.floor_le (by positivity)
      have hK : (k : ℝ)*(A/r)^2 ≤ A/(10*r) := by
        calc
          _ ≤ ((r : ℝ)/(10*A))*(A/r)^2 := mul_le_mul_of_nonneg_right hk (sq_nonneg _)
          _ = _ := by field_simp
      have hsurv : (law p (domainRadiusEvent G S x (3*r))).toReal ≤ A/(5*r) := by
        calc
          _ ≤ A/(10*r)+A/(10*r) := hrecR.trans (add_le_add hV hK)
          _ = _ := by ring
      calc
        _ ≤ (law p (domainRadiusEvent G S x (3*r))).toReal := by
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          apply measure_mono
          rintro ω ⟨y,hc,hd⟩
          exact ⟨y,hc,h3r.trans hd⟩
        _ ≤ A/(5*r) := hsurv
        _ ≤ A/n := div_le_div_of_nonneg_left hA.le
          (show (0 : ℝ) < n by exact_mod_cast hn) (by exact_mod_cast hn5)

theorem critical_intrinsic_radius_upper_of_operator [Infinite V] [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) :
    ∃ A : ℝ, 0 < A ∧ ∀ (S : Set E) x (n : ℕ), 0 < n →
      (law (pc G) (domainRadiusEvent G S x n)).toReal ≤ A/n := by
  obtain ⟨C,hC,hvol⟩ := critical_volume_upper_of_operator_bs G hconn hloc hqt hh hpc1 T hT
  exact intrinsic_radius_upper_of_volume G hloc (pc G)
    (critical_finite_general_bs G hconn hloc hqt hpc1) C hC hvol

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_RadiusTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem extrinsicRadiusEvent_subset_intrinsic (G : BondGraph V E) (x : V) (n : ℕ) :
    extrinsicRadiusEvent G x n ⊆ intrinsicRadiusEvent G x n := by
  rintro ω ⟨y,hc,hd⟩
  refine ⟨y,hc,hd.trans ?_⟩
  have hle : openSimpleGraph G ω ≤ openSimpleGraph G Set.univ := by
    rintro a b ⟨hne,e,he,hab⟩
    exact ⟨hne,e,Set.mem_univ _,hab⟩
  exact SimpleGraph.Reachable.dist_anti hle ((conn_iff_reachable G ω x y).mp hc)

theorem intrinsicRadiusEvent_subset_extrinsic_union (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (x : V) (m n : ℕ) :
    intrinsicRadiusEvent G x m ⊆ extrinsicRadiusEvent G x n ∪
      ⋃ y ∈ (finite_reachBall hloc x n).toFinset, longConnectionEvent G x y m := by
  rintro ω ⟨y,hc,hd⟩
  by_cases he : ω ∈ extrinsicRadiusEvent G x n
  · exact Or.inl he
  · right
    have hdist : graphDistance G x y ≤ n := by
      by_contra h
      exact he ⟨y,hc,(Nat.le_of_lt (Nat.lt_of_not_ge h))⟩
    exact Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr
      ⟨(finite_reachBall hloc x n).mem_toFinset.mpr
        (mem_reachBall_of_graphDistance_le G hconn x y n hdist),hc,hd⟩⟩

theorem intrinsic_radius_le_extrinsic_add [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (x : V) (m n : ℕ) :
    (law p).real (intrinsicRadiusEvent G x m) ≤
      (law p).real (extrinsicRadiusEvent G x n) +
        ((d+1 : ℕ) : ℝ)^n * (2 * ‖T‖ * Real.exp (-(Real.log 2/(3*‖T‖))*m)) := by
  let B := (finite_reachBall hloc x n).toFinset
  let R := 2 * ‖T‖ * Real.exp (-(Real.log 2/(3*‖T‖))*m)
  have hcard : (B.card : ℝ) ≤ ((d+1 : ℕ) : ℝ)^n := by
    have hh := reachBall_ncard_le_pow G hloc d hd x n
    rw [Set.ncard_eq_toFinset_card _ (finite_reachBall hloc x n)] at hh
    exact_mod_cast hh
  calc
    _ ≤ (law p).real (extrinsicRadiusEvent G x n ∪ ⋃ y ∈ B, longConnectionEvent G x y m) :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (intrinsicRadiusEvent_subset_extrinsic_union G hconn hloc x m n))
    _ ≤ (law p).real (extrinsicRadiusEvent G x n) +
        (law p).real (⋃ y ∈ B, longConnectionEvent G x y m) := measureReal_union_le _ _
    _ ≤ (law p).real (extrinsicRadiusEvent G x n) + ∑ y ∈ B, (law p).real (longConnectionEvent G x y m) :=
      add_le_add le_rfl (measureReal_biUnion_finset_le B _)
    _ ≤ (law p).real (extrinsicRadiusEvent G x n) + ∑ _y ∈ B, R := by
      apply add_le_add le_rfl
      exact Finset.sum_le_sum (fun y _ => longConnection_exponential_bound G hloc p T hT x y m)
    _ = (law p).real (extrinsicRadiusEvent G x n) + B.card * R := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (by positivity))

theorem exponential_quadratic_bound {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) ≤ 2/t^2 := by
  have hh := Real.pow_div_factorial_le_exp t ht.le 2
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one] at hh
  rw [Real.exp_neg,inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos t) (sq_pos_of_pos ht)).mpr
  nlinarith

theorem radius_transfer_error {a B c D : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hc : 0 < c) (hD : 0 < D) :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      D^n * (B*Real.exp (-a*(K*n : ℕ))) ≤ (c/(2*K))/n := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (2*Real.log D/a) (16*B/(a^2*c)))
  have hKn : 0 < K := by
    have hh := (le_max_right (2*Real.log D/a) (16*B/(a^2*c))).trans_lt hK
    have : (0 : ℝ) < K := lt_trans (by positivity) hh
    exact_mod_cast this
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKn
  have hlog : 2*Real.log D ≤ a*K := by
    have hh := (le_max_left (2*Real.log D/a) (16*B/(a^2*c))).trans_lt hK
    exact (div_le_iff₀ ha).mp hh.le |>.trans_eq (mul_comm _ _)
  have hsize : 16*B ≤ a^2*c*K := by
    have hh := (le_max_right (2*Real.log D/a) (16*B/(a^2*c))).trans_lt hK
    have h := (div_le_iff₀ (by positivity : 0 < a^2*c)).mp hh.le
    nlinarith
  refine ⟨K,hKn,?_⟩
  intro n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 < a*K*n/2 := by positivity
  have hdecay : D^n * (B*Real.exp (-a*(K*n : ℕ))) ≤ B*Real.exp (-(a*K*n/2)) := by
    have hexp : Real.log D*n - a*K*n ≤ -(a*K*n/2) := by nlinarith
    calc
      _ = B*Real.exp (Real.log D*n-a*K*n) := by
        rw [Real.exp_sub,neg_mul,Real.exp_neg,mul_comm (Real.log D) (n : ℝ),Real.exp_nat_mul,Real.exp_log hD]
        push_cast
        rw [mul_assoc a (K : ℝ) (n : ℝ)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hB.le
  have hpoly := mul_le_mul_of_nonneg_left (exponential_quadratic_bound ht) hB.le
  have hrat : B*(2/(a*K*n/2)^2) ≤ (c/(2*K))/n := by
    have hid : B*(2/(a*K*n/2)^2) = 8*B/(a^2*(K:ℝ)^2*(n:ℝ)^2) := by
      field_simp
      ring
    rw [hid,div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hsize (by positivity : (0 : ℝ) ≤ K*n)
    have hnn := mul_le_mul_of_nonneg_left hn1 (by positivity : (0 : ℝ) ≤ a^2*c*K^2*n)
    nlinarith
  exact hdecay.trans (hpoly.trans hrat)

theorem extrinsic_radius_lower_of_intrinsic [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (x : V) (c : ℝ) (hc : 0 < c)
    (hint : ∀ m : ℕ, 0 < m → c/m ≤ (law p).real (intrinsicRadiusEvent G x m)) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, 0 < n → b/n ≤ (law p).real (extrinsicRadiusEvent G x n) := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  let a := Real.log 2/(3*‖T‖)
  have hnorm : 0 < ‖T‖ := lt_of_lt_of_le zero_lt_one (hT.norm_one_le G p T)
  have ha : 0 < a := div_pos (Real.log_pos (by norm_num)) (by positivity)
  obtain ⟨K,hK,herr⟩ := radius_transfer_error ha (by positivity : 0 < 2*‖T‖) hc
    (by positivity : (0 : ℝ) < (d+1 : ℕ))
  refine ⟨c/(2*K),by positivity,?_⟩
  intro n hn
  have hKn : 0 < K*n := Nat.mul_pos hK hn
  have hlow := hint (K*n) hKn
  have hbound := intrinsic_radius_le_extrinsic_add G hconn hloc p T hT d hd x (K*n) n
  have herror := herr n hn
  have hid : c/(K*n : ℕ) = (c/(2*K))/n + (c/(2*K))/n := by
    push_cast
    field_simp
    ring
  rw [hid] at hlow
  linarith

theorem critical_radius_powerTails_of_operator [Infinite V] [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) (x : V) :
    PowerTail (criticalTail G (intrinsicRadiusEvent G) x) 1 ∧
      PowerTail (criticalTail G (extrinsicRadiusEvent G) x) 1 := by
  obtain ⟨c,hc,hlo⟩ := critical_intrinsic_radius_lower_of_operator G hconn hloc hqt hh hpc1 T hT x
  obtain ⟨C,hC,hup⟩ := critical_intrinsic_radius_upper_of_operator G hconn hloc hqt hh hpc1 T hT
  have hint (n : ℕ) (hn : 0 < n) : criticalTail G (intrinsicRadiusEvent G) x n ≤ C/n := by
    change (law (pc G) (intrinsicRadiusEvent G x n)).toReal ≤ C/n
    simpa only [domainRadiusEvent,Set.inter_univ,Set.ofPred_mem_eq] using hup Set.univ x n hn
  obtain ⟨b,hb,hext⟩ := extrinsic_radius_lower_of_intrinsic G hconn hloc hqt (pc G) T hT x c hc hlo
  have hupper (n : ℕ) (hn : 0 < n) : criticalTail G (extrinsicRadiusEvent G) x n ≤ C/n := by
    apply le_trans _ (hint n hn)
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (extrinsicRadiusEvent_subset_intrinsic G x n))
  constructor
  · refine ⟨c,C,hc,hC,fun n hn => ?_⟩
    simpa only [Real.rpow_neg_one,div_eq_mul_inv] using And.intro (hlo n hn) (hint n hn)
  · refine ⟨b,C,hb,hC,fun n hn => ?_⟩
    have hlow : b/n ≤ criticalTail G (extrinsicRadiusEvent G) x n := hext n hn
    simpa only [Real.rpow_neg_one,div_eq_mul_inv] using And.intro hlow (hupper n hn)

theorem criticalRadiiInput_of_nonamenable_bs_oai [Infinite V]
    (G : BondGraph V E) (hh : 0 < hV G) : HutchcroftCriticalRadiiInput G := by
  intro hgraph hgap x
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  have hp1 : (pc G : ℝ) < 1 :=
    (show (pc G : ℝ) < (ptwo G : ℝ) from hgap).trans_le (ptwo G).2.2
  obtain ⟨q,hq,hpq⟩ := lt_sSup_iff.mp hgap
  obtain ⟨T,hT⟩ := operatorBounded_of_le G hpq.le hq
  have hfin := critical_finite_general_bs G hgraph.connected hgraph.locallyFinite hgraph.quasiTransitive hp1
  rw [criticalFiniteTail_eq G (intrinsicRadiusEvent G) x (hfin x),
    criticalFiniteTail_eq G (extrinsicRadiusEvent G) x (hfin x)]
  exact critical_radius_powerTails_of_operator G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hh hp1 T hT x

end Percolation.BenjaminiSchramm

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs_oai.{u, v} := @OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs_oai.{u, v}
