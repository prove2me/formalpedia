-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:10:26.377399+00:00
-- url     : https://prove2.me/submissions/abe72a56-c85a-4ccc-9efd-8c737184a1dd

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_atMostOneHeavy_critical_ae_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_critical_null_of_compact_open_orbital_quotient_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_main_light_or_sparse_polynomial_boundary_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_nonunimodular_critical_mass_finite_ae_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_nonunimodular_critical_twoPoint_decay_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_nonunimodular_no_percolation_at_criticality_bs

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)

theorem countable_vertices (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable V := by
  obtain ⟨o⟩ := hconnected.nonempty
  have hc : (⋃ n : ℕ, G.vertexBall o n).Countable :=
    Set.countable_iUnion fun n => (G.vertexBall_finite hlocal o n).countable
  have heq : (⋃ n : ℕ, G.vertexBall o n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n, hn⟩ := G.reachable_mem_vertexBall (hconnected o v)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

theorem countable_bonds (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable E := by
  let := G.countable_vertices hconnected hlocal
  have hc : (⋃ v : V, {e : E | v ∈ G.ends e}).Countable :=
    Set.countable_iUnion fun v => (hlocal v).countable
  have heq : (⋃ v : V, {e : E | v ∈ G.ends e}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    exact Set.mem_iUnion.mpr ⟨(G.ends e).out.1, Sym2.out_fst_mem _⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

lemma measurable_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact Measurable.of_eval fun vertex => G.measurable_reachable v vertex

lemma measurable_infinite_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => (G.cluster ω v).Infinite) := by
  simp_rw [← Set.encard_eq_top_iff]
  exact (measurable_encard.comp (G.measurable_cluster v)).eq_const ⊤

theorem measurableSet_percolates [Countable V] [Countable E] :
    MeasurableSet G.percolates := by
  exact (Measurable.exists fun v => G.measurable_infinite_cluster v).setOf

lemma law_zero_percolates [Countable V] [Countable E] : G.law 0 G.percolates = 0 := by
  rw [law, ProbabilityTheory.setBernoulli_zero,
    Measure.dirac_apply' _ G.measurableSet_percolates]
  simp

lemma mem_cluster_finite_witness {ω : Set E} {v w : V} (h : w ∈ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v := by
  classical
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp h
  clear h
  induction hr with
  | refl => exact ⟨∅, Set.finite_empty, Set.empty_subset _, .refl _⟩
  | @tail u w hr huw ih =>
      obtain ⟨s, hs, hsω, hvs⟩ := ih
      obtain ⟨⟨e, heω, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      refine ⟨insert e s, hs.insert e, Set.insert_subset heω hsω, ?_⟩
      have hvu : (G.openGraph (insert e s)).Reachable v u :=
        hvs.mono (G.openGraph_mono (Set.subset_insert _ _))
      apply hvu.trans
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, Set.mem_insert _ _, heq⟩, hne⟩

lemma finite_subset_cluster_finite_witness {ω : Set E} {v : V} {K : Set V}
    (hK : K.Finite) (hKv : K ⊆ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ K ⊆ G.cluster s v := by
  classical
  have h : ∀ w ∈ K, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v :=
    fun w hw => G.mem_cluster_finite_witness (hKv hw)
  choose s hs hsω hws using h
  let := hK.fintype
  refine ⟨⋃ w : K, s w w.property, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun w => hs w w.property
  · exact Set.iUnion_subset fun w => hsω w w.property
  · intro w hw
    exact G.cluster_mono (Set.subset_iUnion (fun w : K => s w w.property) ⟨w, hw⟩)
      v (hws w hw)

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

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

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_image_equiv (e : E ≃ E) :
    Measurable (fun ω : Set E => e '' ω) := by
  have he : (fun ω : Set E => e '' ω) = (fun ω => e.symm ⁻¹' ω) := by
    funext ω
    ext i
    simp
  rw [he]
  exact Measurable.of_eval (fun index => measurable_set_mem (e.symm index))

lemma law_map_equiv (p : unitInterval) (e : E ≃ E) :
    (law (fun _ : E => p)).map (fun ω : Set E => e '' ω) = law (fun _ : E => p) := by
  unfold law
  rw [Measure.map_map (measurable_image_equiv e) MeasurableEquiv.setOfPred.measurable]
  have he : (fun ω : Set E => e '' ω) ∘ MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ MeasurableEquiv.piCongrLeft (fun _ : E => Prop) e := by
    funext ω
    ext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_piCongrLeft (fun _ : E => bitMeasure p) e]

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.cluster_image (φ : G.Aut) (ω : Set E) (o : V) :
    φ.vertex '' G.cluster ω o = G.cluster (φ.edge '' ω) (φ.vertex o) := by
  ext v
  obtain ⟨w, rfl⟩ := φ.vertex.surjective v
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]
  change (G.openGraph ω).Reachable o w ↔
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex o) (φ.vertex w)
  exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := o) (v := w)).symm

lemma law_map_aut (p : unitInterval) (φ : G.Aut) :
    (G.law p).map (fun ω : Set E => φ.edge '' ω) = G.law p := by
  simpa only [BernoulliProduct.law_const, law] using
    BernoulliProduct.law_map_equiv p φ.edge

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphBalls
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.vertexBall_image (φ : G.Aut) (o : V) (n : ℕ) :
    φ.vertex '' G.vertexBall o n = G.vertexBall (φ.vertex o) n := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using
    (Aut.vertexBall_mem G φ o w n).symm

lemma orbit_density_radius (hconnected : G.fullGraph.Connected)
    (hquasi : G.QuasiTransitive) (u : V) :
    ∃ C : ℕ, ∀ v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  have hpath : ∀ z : S, ∃ n, u ∈ G.vertexBall z.val n :=
    fun z => G.reachable_mem_vertexBall (hconnected z u)
  choose n hn using hpath
  let := hS.fintype
  let C := ∑ z : S, n z
  refine ⟨C,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  refine ⟨φ,(Aut.vertexBall_mem G φ z u C).mpr ?_⟩
  exact G.vertexBall_mono z (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨z,hz⟩ : S))) (hn ⟨z,hz⟩)

end CriticalPercolation.BondGraph
end
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteEnergy
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
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_coordinate (q : E → unitInterval) (e : E) (b : Prop) :
    law q {ω : Set E | (e ∈ ω) = b} = bitMeasure (q e) {b} := by
  rw [law_eq_infinitePi]
  have h := congrArg (fun μ : Measure Prop => μ {b})
    (Measure.infinitePi_map_eval (fun e => bitMeasure (q e)) e)
  rw [Measure.map_apply (measurable_pi_apply e) (MeasurableSet.singleton b)] at h
  exact h

lemma force_singleton_preimage_null (q : E → unitInterval) (e : E) (σ : Set E)
    (hb : bitMeasure (q e) {e ∈ σ} ≠ 0)
    (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q (forceOn {e} σ ⁻¹' A) = 0 := by
  let B := forceOn {e} σ ⁻¹' A
  let C := {ω : Set E | (e ∈ ω) = (e ∈ σ)}
  have hmC : MeasurableSet[blockSigma {e}] C := by
    have hc : MeasurableSet[coordinateSigma e] C :=
      ⟨{e ∈ σ}, MeasurableSet.singleton _, rfl⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Set.mem_singleton e) le_rfl) :
      coordinateSigma e ≤ blockSigma {e}) _ hc
  have hmB : MeasurableSet[blockSigma ({e} : Set E)ᶜ] B :=
    hA.preimage (measurable_forceOn_block {e} σ)
  have hmul := ((independent_blocks q {e}).indepSet_of_measurableSet hmC hmB).measure_inter_eq_mul
  have hsub : C ∩ B ⊆ A := by
    intro ω hω
    have heq : forceOn {e} σ ω = ω := by
      ext f
      change (if f ∈ ({e} : Set E) then f ∈ σ else f ∈ ω) ↔ f ∈ ω
      by_cases hf : f = e
      · subst f
        simpa only [Set.mem_singleton_iff, ↓reduceIte] using (Iff.of_eq hω.1.symm)
      · simp only [Set.mem_singleton_iff, ite_eq_right hf]
    have hh : forceOn {e} σ ω ∈ A := hω.2
    rwa [heq] at hh
  have hz : law q (C ∩ B) = 0 := measure_mono_null hsub hnull
  rw [hz, law_coordinate] at hmul
  exact (mul_eq_zero.mp hmul.symm).resolve_left hb

lemma bitMeasure_true_ne_zero (p : unitInterval) (hp : (0:ℝ) < p) :
    bitMeasure p {True} ≠ 0 := by
  have hh := bitMeasure_real_singleton p True
  simp only [bitWeight, if_true] at hh
  intro hz
  have : (bitMeasure p).real {True} = 0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  rw [hh] at this
  exact (ne_of_gt hp) this

lemma insert_preimage_null (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (e : E) (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q ((fun ω => insert e ω) ⁻¹' A) = 0 := by
  have hh := force_singleton_preimage_null q e Set.univ (bitMeasure_true_ne_zero (q e) (hq e))
    A hA hnull
  have heq : forceOn {e} Set.univ = (fun ω : Set E => insert e ω) := by
    funext ω
    ext f
    change (if f ∈ ({e} : Set E) then True else f ∈ ω) ↔ (f = e ∨ f ∈ ω)
    simp only [Set.mem_singleton_iff]
    split_ifs <;> tauto
  rwa [heq] at hh

lemma measurable_union_left (S : Set E) : Measurable (fun ω : Set E => S ∪ ω) :=
  Measurable.of_eval (fun edge => measurable_const.or (measurable_set_mem edge))

lemma finite_union_preimage_null (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (S : Set E) (hS : S.Finite) (A : Set (Set E)) (hA : MeasurableSet A)
    (hnull : law q A = 0) : law q ((fun ω => S ∪ ω) ⁻¹' A) = 0 := by
  induction S,hS using Set.Finite.induction_on generalizing A with
  | empty =>
    have hh : (fun ω : Set E => (∅ : Set E) ∪ ω) = id := funext (fun _ => Set.empty_union _)
    rw [hh,Set.preimage_id_eq]
    exact hnull
  | @insert e S he hS ih =>
    have hi := insert_preimage_null q hq e A hA hnull
    have hm : Measurable (fun ω : Set E => insert e ω) := by
      simpa only [Set.singleton_union] using measurable_union_left ({e} : Set E)
    have hh := ih ((fun ω => insert e ω) ⁻¹' A) (hA.preimage hm) hi
    simpa only [Set.preimage_preimage,Function.comp_def,Set.insert_union] using hh

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BlockIndependence
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
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma blockSigma_mono {S T : Set E} (h : S ⊆ T) : blockSigma S ≤ blockSigma T := by
  apply iSup₂_le
  intro e he
  exact le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)

lemma independent_disjoint_blocks (q : E → unitInterval) (S T : Set E)
    (h : Disjoint S T) : Indep (blockSigma S) (blockSigma T) (law q) :=
  indep_iSup_of_disjoint coordinateSigma_le (independent_coordinates q) h

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteIndexAction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ Q : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

lemma subgroup_preservesEnds (ha : G.PreservesEnds (Λ := Λ)) (L : Subgroup Λ) :
    G.PreservesEnds (Λ := L) := fun g e => ha g.val e

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitQuotientTransfer
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ Q Y : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

lemma finite_kernel_orbits_from_one_vertex
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ)) (ρ : Λ →* Q) (o : V)
    (ho : (MulAction.orbit ρ.ker o).Finite) :
    ∀ v : V, (MulAction.orbit ρ.ker v).Finite := by
  intro v
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc o v)
  have hfin := ho.biUnion (fun w _ => G.vertexBall_finite hl w n)
  apply hfin.subset
  rintro w ⟨g,rfl⟩
  refine Set.mem_iUnion₂.mpr ⟨g.val • o,⟨g,rfl⟩,?_⟩
  exact (Aut.vertexBall_mem G (G.smulAut ha g.val) o v n).mpr hn

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitalPower
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma powerOn_reachable_of_close {O : Set V} {L : ℕ} (u v : O)
    (h : v.val∈G.vertexBall u.val L) : (G.powerOn O L).Reachable u v := by
  by_cases huv : u=v
  · rw [huv]
  · exact SimpleGraph.Adj.reachable (⟨huv,h⟩ : (G.powerOn O L).Adj u v)

lemma powerOn_reachable_lift {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C)
    {x y : V} (p : G.fullGraph.Walk x y) (u v : O)
    (hu : u.val∈G.vertexBall x C) (hv : v.val∈G.vertexBall y C) :
    (G.powerOn O (2*C+1)).Reachable u v := by
  induction p generalizing u with
  | nil =>
    apply G.powerOn_reachable_of_close
    exact G.vertexBall_mono u.val (by omega)
      (G.vertexBall_add (G.vertexBall_comm.mp hu) C hv)
  | @cons x z y hxz p ih =>
    obtain ⟨w,hw⟩ := hdense z
    apply SimpleGraph.Reachable.trans (v := w)
    · apply G.powerOn_reachable_of_close
      have hz := G.vertexBall_step (G.vertexBall_comm.mp hu) hxz
      have hvw := G.vertexBall_add hz C hw
      simpa only [show C+1+C=2*C+1 by omega] using hvw
    · exact ih w hw hv

lemma powerOn_connected (hc : G.fullGraph.Connected) {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C) :
    (G.powerOn O (2*C+1)).Connected := by
  let _ := hc.nonempty
  obtain ⟨o⟩ := ‹Nonempty V›
  obtain ⟨u,_⟩ := hdense o
  let _ : Nonempty O := ⟨u⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨p⟩ := hc x.val y.val
  exact G.powerOn_reachable_lift hdense p x y
    (G.mem_vertexBall_self x.val C) (G.mem_vertexBall_self y.val C)

lemma powerOn_finite_neighbors (hl : G.LocallyFinite) (O : Set V) (L : ℕ) (u : O) :
    ((G.powerOn O L).neighborSet u).Finite := by
  apply (Set.Finite.preimage Subtype.val_injective.injOn (G.vertexBall_finite hl u.val L)).subset
  exact fun _ h => h.2

lemma powerOn_walk_bound {O : Set V} {L : ℕ} {u v : O}
    (p : (G.powerOn O L).Walk u v) :
    v.val∈G.vertexBall u.val (L*p.length) := by
  induction p with
  | nil => exact G.mem_vertexBall_self _ _
  | @cons u w v huw p ih =>
    simpa only [SimpleGraph.Walk.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm]
      using G.vertexBall_add huw.2 (L*p.length) ih

lemma powerOn_ball_bound {O : Set V} {L n : ℕ} (u : O) :
    {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n} ⊆
      Subtype.val ⁻¹' G.vertexBall u.val (L*n) := by
  rintro v ⟨p,hp⟩
  exact G.vertexBall_mono u.val (Nat.mul_le_mul_left _ hp) (G.powerOn_walk_bound p)

lemma powerOn_ball_card_le (hl : G.LocallyFinite) {O : Set V} {L n C R : ℕ}
    (x : V) (u : O) (hu : u.val∈G.vertexBall x C) (hR : C+L*n≤R) :
    {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n}.ncard ≤
      (G.vertexBall x R).ncard := by
  have hh : {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n} ⊆
      Subtype.val ⁻¹' G.vertexBall x R := by
    intro v hv
    exact G.vertexBall_mono x hR (G.vertexBall_add hu (L*n) (G.powerOn_ball_bound u hv))
  calc
    _ = (Subtype.val '' {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n}).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.vertexBall x R).ncard := Set.ncard_le_ncard (Set.image_subset_iff.mpr hh)
      (G.vertexBall_finite hl x R)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitalAction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitPower_connected (hc : G.fullGraph.Connected) (hq : G.QuasiTransitive)
    (o : V) : ∃ C : ℕ, (G.orbitPower o (2*C+1)).Connected ∧
      (∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C) := by
  obtain ⟨C,hC⟩ := G.orbit_density_radius hc hq o
  have hd : ∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C := by
    intro v
    obtain ⟨φ,hφ⟩ := hC v
    exact ⟨⟨φ.vertex o,⟨φ,rfl⟩⟩,hφ⟩
  exact ⟨C,G.powerOn_connected hc hd,hd⟩

lemma orbitPower_ball_ncard (o : V) (L n : ℕ) (u v : MulAction.orbit G.Aut o) :
    {w | ∃ p : (G.orbitPower o L).Walk u w, p.length≤n}.ncard =
    {w | ∃ p : (G.orbitPower o L).Walk v w, p.length≤n}.ncard := by
  obtain ⟨φ,hφ⟩ := MulAction.exists_smul_eq G.Aut u v
  subst v
  let f := G.orbitPowerHom o L φ
  have he : f '' {w | ∃ p : (G.orbitPower o L).Walk u w, p.length≤n} =
      {w | ∃ p : (G.orbitPower o L).Walk (φ • u) w, p.length≤n} := by
    ext w
    constructor
    · rintro ⟨z,⟨p,hp⟩,rfl⟩
      exact ⟨p.map f.toHom,(SimpleGraph.Walk.length_map f.toHom p).le.trans hp⟩
    · rintro ⟨p,hp⟩
      refine ⟨f.symm w,?_,f.apply_symm_apply w⟩
      have hp' : ∃ q : (G.orbitPower o L).Walk (f.symm (f u)) (f.symm w), q.length≤n :=
        ⟨p.map f.symm.toHom,(SimpleGraph.Walk.length_map f.symm.toHom p).le.trans hp⟩
      rw [show f.symm (f u)=u from f.symm_apply_apply u] at hp'
      exact hp'
  rw [← he,Set.ncard_image_of_injective _ f.injective]

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitalScales
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma dense_set_infinite [Infinite V] (hl : G.LocallyFinite) {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C) : O.Infinite := by
  intro hO
  have hh : (⋃ u∈O, G.vertexBall u C).Finite :=
    hO.biUnion (fun u _ => G.vertexBall_finite hl u C)
  apply Set.infinite_univ.not_finite (hh.subset ?_)
  intro v _
  obtain ⟨u,hu⟩ := hdense v
  exact Set.mem_iUnion₂.mpr ⟨u.val,u.property,G.vertexBall_comm.mp hu⟩

lemma polynomial_scale_arithmetic (C L d N R : ℕ) (hL : 0<L)
    (hR : C+L*(max N ((C+2*L)^d)+1)≤R) :
    let n := (R-C)/L
    N≤n ∧ C+L*n≤R ∧ R^d≤n^(d+1) := by
  dsimp
  let n := (R-C)/L
  change N≤n ∧ C+L*n≤R ∧ R^d≤n^(d+1)
  have hC : C≤R := by omega
  have hsub : R-C+C=R := Nat.sub_add_cancel hC
  have hN : max N ((C+2*L)^d)+1≤n := by
    apply (Nat.le_div_iff_mul_le hL).mpr
    nlinarith
  have hn : 1≤n := by omega
  have hmul : L*n≤R-C := by
    dsimp [n]
    exact Nat.mul_div_le (R-C) L
  have hmod : R-C<L*n+L := by
    have he := Nat.div_add_mod (R-C) L
    have ht := Nat.mod_lt (R-C) hL
    dsimp [n]
    nlinarith
  have hcn : C+L≤(C+L)*n := by nlinarith [Nat.mul_le_mul_left (C+L) hn]
  have hupper : R≤(C+2*L)*n := by nlinarith
  refine ⟨by omega,by omega,?_⟩
  calc
    R^d ≤ ((C+2*L)*n)^d := Nat.pow_le_pow_left hupper d
    _ = (C+2*L)^d*n^d := Nat.mul_pow _ _ _
    _ ≤ n*n^d := Nat.mul_le_mul_right _ (by omega)
    _ = n^(d+1) := by rw [pow_succ,Nat.mul_comm]

theorem orbital_power_polynomial_scales (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∃ C : ℕ, (G.orbitPower o (2*C+1)).Connected ∧
      (∀ x, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall x C) ∧
      (∀ N : ℕ, ∃ n≥N, ∀ u : MulAction.orbit G.Aut o,
        {v | ∃ p : (G.orbitPower o (2*C+1)).Walk u v, p.length≤n}.ncard≤n^(d+1)) := by
  obtain ⟨C,hC,hdense⟩ := G.orbitPower_connected hc hq o
  refine ⟨C,hC,hdense,?_⟩
  intro N
  let L := 2*C+1
  obtain ⟨R,hR,x,hx⟩ := hpoly (C+L*(max N ((C+2*L)^d)+1))
  obtain ⟨u,hu⟩ := hdense x
  have hh := polynomial_scale_arithmetic C L d N R (by dsimp [L]; omega) hR
  dsimp only at hh
  refine ⟨(R-C)/L,hh.1,?_⟩
  intro v
  rw [G.orbitPower_ball_ncard o L ((R-C)/L) v u]
  exact (G.powerOn_ball_card_le hl x u hu hh.2.1).trans (hx.trans hh.2.2)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_SparseDoubling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

lemma sparse_polynomial_doubling_scales (f : ℕ → ℕ) (hf : Monotone f)
    (hpos : ∀ n, 1≤f n) (d : ℕ) (hpoly : ∀ R, ∃ n≥R, f n≤n^d) :
    ∀ R : ℕ, ∃ n≥R, f (5*n)≤5^(d+1)*f n := by
  intro R
  by_contra! hbad
  let A := max R 1
  have hA : 0<A := by dsimp [A]; omega
  have hRA : R≤A := le_max_left _ _
  have hgrow : ∀ k : ℕ, (5^(d+1))^k≤f (5^k*A) := by
    intro k
    induction k with
    | zero => simpa using hpos A
    | succ k ih =>
      have hbase : R≤5^k*A := hRA.trans (by
        have : 1≤5^k := Nat.one_le_pow k 5 (by omega)
        nlinarith)
      have hh := (hbad (5^k*A) hbase).le
      calc
        (5^(d+1))^(k+1) = 5^(d+1)*(5^(d+1))^k := by rw [pow_succ]; ring
        _ ≤ 5^(d+1)*f (5^k*A) := Nat.mul_le_mul_left _ ih
        _ ≤ f (5*(5^k*A)) := hh
        _ = f (5^(k+1)*A) := by congr 1; rw [pow_succ]; ring
  obtain ⟨n,hn,hnpoly⟩ := hpoly (5*A*((5*A)^d+1))
  have hnA : 5*((5*A)^d+1)≤n/A := by
    apply (Nat.le_div_iff_mul_le hA).mpr
    nlinarith
  have hnApos : n/A≠0 := by omega
  let k := Nat.log 5 (n/A)
  let P := 5^k
  have hP : P≤n/A := Nat.pow_log_le_self 5 hnApos
  have hP' : n/A<5*P := by
    have hh := Nat.lt_pow_of_log_lt (b := 5) (x := k+1) (y := n/A) (by omega)
      (show Nat.log 5 (n/A)<k+1 by omega)
    simpa only [pow_succ,Nat.mul_comm] using hh
  have hPL : (5*A)^d<P := by nlinarith
  have hPA : P*A≤n := (Nat.le_div_iff_mul_le hA).mp hP
  have hnupper : n<(5*P)*A := (Nat.div_lt_iff_lt_mul hA).mp hP'
  have hPP : 5^((d+1)*k)≤f n := by
    rw [pow_mul]
    exact (hgrow k).trans (hf hPA)
  have hform : 5^((d+1)*k)=P^d*P := by
    dsimp [P]
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  rw [hform] at hPP
  have hupper : n^d≤P^d*(5*A)^d := by
    have hh := Nat.pow_le_pow_left hnupper.le d
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hPpos : 0<P^d := pow_pos (by dsimp [P]; positivity) d
  have hlt : P^d*(5*A)^d<P^d*P := Nat.mul_lt_mul_of_pos_left hPL hPpos
  exact (not_lt_of_ge (hPP.trans (hnpoly.trans hupper))) hlt

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_OrbitalNeighborhoods
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical Pointwise

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitBall_finite (hl : G.LocallyFinite) (o : V) (r : ℕ) :
    (G.orbitBall o r).Finite := (G.vertexBall_finite hl o r).subset Set.inter_subset_right

lemma Aut.orbitBall_mem (φ : G.Aut) (o v : V) (r : ℕ) :
    φ • v ∈ G.orbitBall (φ • o) r ↔ v ∈ G.orbitBall o r := by
  change (φ • v ∈ MulAction.orbit G.Aut (φ • o) ∧
    φ.vertex v ∈ G.vertexBall (φ.vertex o) r) ↔ _
  rw [Aut.vertexBall_mem]
  refine and_congr ?_ Iff.rfl
  rw [MulAction.orbit_smul]
  constructor
  · rintro ⟨ψ,hψ⟩
    refine ⟨φ⁻¹*ψ,?_⟩
    change (φ⁻¹*ψ) • o=v
    change ψ • o=φ • v at hψ
    rw [mul_smul,hψ,inv_smul_smul]
  · rintro ⟨ψ,rfl⟩
    exact ⟨φ*ψ,mul_smul _ _ _⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitalFiniteGeneration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitPower_propagate_subgroup_orbit (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (hgen : ∀ v∈G.orbitBall o L, v∈MulAction.orbit Λ o)
    {u v : MulAction.orbit G.Aut o} (huv : (G.orbitPower o L).Adj u v)
    (hu : u.val∈MulAction.orbit Λ o) : v.val∈MulAction.orbit Λ o := by
  obtain ⟨φ,hφ⟩ := hu
  change φ.val • o=u.val at hφ
  have hv : v.val∈G.orbitBall (φ.val • o) L := by
    refine ⟨?_,?_⟩
    · simpa only [MulAction.orbit_smul] using v.property
    · rw [hφ]
      exact huv.2
  have hback : φ.val⁻¹ • v.val∈G.orbitBall o L := by
    have hh := (Aut.orbitBall_mem G φ.val o (φ.val⁻¹ • v.val) L)
    rw [smul_inv_smul] at hh
    exact hh.mp hv
  obtain ⟨ψ,hψ⟩ := hgen _ hback
  refine ⟨φ*ψ,?_⟩
  change (φ*ψ) • o=v.val
  change ψ • o=φ.val⁻¹ • v.val at hψ
  rw [mul_smul,hψ]
  change φ.val • (φ.val⁻¹ • v.val)=v.val
  exact smul_inv_smul _ _

lemma orbitPower_subgroup_transitive (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (hc : (G.orbitPower o L).Connected)
    (hgen : ∀ v∈G.orbitBall o L, v∈MulAction.orbit Λ o) :
    MulAction.orbit Λ o=MulAction.orbit G.Aut o := by
  apply Set.Subset.antisymm
  · rintro v ⟨φ,hφ⟩
    exact ⟨φ.val,hφ⟩
  · intro v hv
    let o' : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
    let v' : MulAction.orbit G.Aut o := ⟨v,hv⟩
    obtain ⟨p⟩ := hc o' v'
    have hwalk : ∀ {u w : MulAction.orbit G.Aut o} (p : (G.orbitPower o L).Walk u w),
        u.val∈MulAction.orbit Λ o → w.val∈MulAction.orbit Λ o := by
      intro u w p
      induction p with
      | nil => exact id
      | cons huw p ih =>
        exact fun hu => ih (G.orbitPower_propagate_subgroup_orbit o L Λ hgen huw hu)
    exact hwalk p (MulAction.mem_orbit_self o)

lemma dense_orbit_subgroup_representatives (o : V)
    (C : ℕ) (hdense : ∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C)
    (Λ : Subgroup G.Aut) (horbit : MulAction.orbit Λ o=MulAction.orbit G.Aut o) :
    ∀ v, ∃ s∈G.vertexBall o C, v∈MulAction.orbit Λ s := by
  intro v
  obtain ⟨u,hu⟩ := hdense v
  have hu' : u.val∈MulAction.orbit Λ o := by rw [horbit]; exact u.property
  obtain ⟨φ,hφ⟩ := hu'
  change φ.val • o=u.val at hφ
  refine ⟨φ.val⁻¹ • v,?_,φ,?_⟩
  · apply (Aut.vertexBall_mem G φ.val o (φ.val⁻¹ • v) C).mp
    change φ.val • (φ.val⁻¹ • v)∈G.vertexBall (φ.val • o) C
    rw [smul_inv_smul,hφ]
    exact G.vertexBall_comm.mp hu
  · change φ.val • (φ.val⁻¹ • v)=v
    exact smul_inv_smul _ _

theorem finitelyGenerated_quasiTransitive_subgroup (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) :
    ∃ Λ : Subgroup G.Aut, Group.FG Λ ∧
      MulAction.orbit Λ o=MulAction.orbit G.Aut o ∧
      ∃ S : Set V, S.Finite ∧ ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s := by
  obtain ⟨C,hC,hdense⟩ := G.orbitPower_connected hc hq o
  let B := G.orbitBall o (2*C+1)
  have hB : B.Finite := G.orbitBall_finite hl o _
  let _ := hB.fintype
  have hφ : ∀ v : B, ∃ φ : G.Aut, φ • o=v.val := fun v => v.property.1
  choose φ hφ using hφ
  let F := Finset.univ.image φ
  let Λ := Subgroup.closure (F : Set G.Aut)
  have hgen : ∀ v∈G.orbitBall o (2*C+1), v∈MulAction.orbit Λ o := by
    intro v hv
    have hf : φ ⟨v,hv⟩∈Λ := Subgroup.subset_closure
      (Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩)
    exact ⟨⟨φ ⟨v,hv⟩,hf⟩,hφ ⟨v,hv⟩⟩
  have horbit := G.orbitPower_subgroup_transitive o (2*C+1) Λ hC hgen
  refine ⟨Λ,inferInstance,horbit,G.vertexBall o C,G.vertexBall_finite hl o C,?_⟩
  exact G.dense_orbit_subgroup_representatives o C hdense Λ horbit

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_OpenTrialBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexBalls_disjoint {v w : V} {n : ℕ} (h : w∉G.vertexBall v (n+n)) :
    Disjoint (G.vertexBall v n) (G.vertexBall w n) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact h (G.vertexBall_add hz n (G.vertexBall_comm.mp hz'))

lemma inducedEdges_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (G.inducedEdges S) (G.inducedEdges T) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
  have hx : x∈G.ends e := by rw [← hxy]; simp
  exact Set.disjoint_left.mp h (he x hx) (he' x hx)

end BondGraph
end CriticalPercolation
end
end
end

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularLevelGeometry
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

attribute [local instance] OAI.CriticalPercolation.BondGraph.instMulActionAut_1
lemma aut_preservesEnds : G.PreservesEnds (Λ := G.Aut) := fun φ => φ.preserves

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_FaithfulOrbitalModel
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitalActionMap_kernel_fixes (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (φ : (G.orbitalActionMap o L Λ).ker) : φ • o=o := by
  have hh := congrArg Subtype.val φ.property
  change (G.orbitPowerHom o L φ.val.val) = 1 at hh
  let o' : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
  have ho := congrArg (fun f : G.orbitPower o L ≃g G.orbitPower o L => (f o').val) hh
  exact ho

lemma orbitalActionMap_finite_kernel_orbits (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    ∀ v : V, (MulAction.orbit (G.orbitalActionMap o L Λ).ker v).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.finite_kernel_orbits_from_one_vertex hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) (G.orbitalActionMap o L Λ) o
  apply (Set.finite_singleton o).subset
  rintro v ⟨φ,rfl⟩
  exact G.orbitalActionMap_kernel_fixes o L Λ φ

lemma orbitalActionGroup_transitive (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (horbit : MulAction.orbit Λ o=MulAction.orbit G.Aut o)
    (u v : MulAction.orbit G.Aut o) :
    ∃ φ : G.orbitalActionGroup o L Λ, φ.val u=v := by
  have hu : u.val∈MulAction.orbit Λ o := by rw [horbit]; exact u.property
  have hv : v.val∈MulAction.orbit Λ o := by rw [horbit]; exact v.property
  obtain ⟨a,ha⟩ := hu
  obtain ⟨b,hb⟩ := hv
  refine ⟨G.orbitalActionMap o L Λ (b*a⁻¹),?_⟩
  apply Subtype.ext
  change (b*a⁻¹) • u.val=v.val
  change a • o=u.val at ha
  change b • o=v.val at hb
  rw [←ha,mul_smul,inv_smul_smul,hb]

theorem sparse_polynomial_faithful_orbital_model [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∃ C : ℕ, ∃ Λ : Subgroup G.Aut, Group.FG Λ ∧
      (G.orbitPower o (2*C+1)).Connected ∧
      (MulAction.orbit G.Aut o).Infinite ∧
      (∀ u, ((G.orbitPower o (2*C+1)).neighborSet u).Finite) ∧
      (∀ u v, ∃ φ : G.orbitalActionGroup o (2*C+1) Λ, φ.val u=v) ∧
      (∀ v : V, (MulAction.orbit (G.orbitalActionMap o (2*C+1) Λ).ker v).Finite) ∧
      (∃ S : Set V, S.Finite ∧ ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) ∧
      (∀ R : ℕ, ∃ n≥R, ∀ u : MulAction.orbit G.Aut o,
        {v | ∃ p : (G.orbitPower o (2*C+1)).Walk u v, p.length≤n}.ncard≤n^(d+1)) := by
  obtain ⟨C,hC,hdense,hscales⟩ := G.orbital_power_polynomial_scales hc hl hq o d hpoly
  obtain ⟨Λ,hΛ,horbit,hreps⟩ := G.finitelyGenerated_quasiTransitive_subgroup hc hl hq o
  refine ⟨C,Λ,hΛ,hC,G.dense_set_infinite hl hdense,?_,?_,?_,hreps,hscales⟩
  · exact G.powerOn_finite_neighbors hl _ _
  · exact G.orbitalActionGroup_transitive o (2*C+1) Λ horbit
  · exact G.orbitalActionMap_finite_kernel_orbits hc hl o (2*C+1) Λ

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BallIncidence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.inducedEdges_map (φ : G.Aut) {K : Set E} {S : Set V}
    (hKS : K⊆G.inducedEdges S) : φ.edge '' K ⊆ G.inducedEdges (φ.vertex '' S) := by
  rintro e ⟨a,ha,rfl⟩ v hv
  rw [φ.preserves] at hv
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨w,hKS ha w hw,rfl⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

omit [Fintype V] in
lemma cluster_eq_of_reachable {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : G.cluster ω u = G.cluster ω v := by
  ext z
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_PercolationTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_union_subset (ω S : Set E) (o : V) :
    G.cluster (ω ∪ S) o ⊆ G.cluster ω o ∪
      ⋃ e ∈ S, ⋃ v ∈ (G.ends e).toFinset, G.cluster ω v := by
  intro z hz
  have hr := ((G.openGraph (ω ∪ S)).reachable_iff_reflTransGen o z).mp hz
  clear hz
  induction hr with
  | refl => exact Or.inl (.refl _)
  | @tail x y hr hxy ih =>
    obtain ⟨⟨e, he, heq⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    rcases he with he | he
    · have hadj : (G.openGraph ω).Adj x y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩
      rcases ih with ho | h
      · exact Or.inl (ho.trans hadj.reachable)
      · obtain ⟨f,hf,h⟩ := Set.mem_iUnion₂.mp h
        obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp h
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,Set.mem_iUnion₂.mpr
          ⟨v,hv,hh.trans hadj.reachable⟩⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr
        ⟨y,by simp [heq], .refl _⟩⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_FiniteClusterCover
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infinite_cluster_union_has_old (ω J : Set E) (hJ : J.Finite) (o : V)
    (ho : (G.cluster (ω ∪ J) o).Infinite) :
    ∃ v, (G.openGraph (ω ∪ J)).Reachable o v ∧ (G.cluster ω v).Infinite := by
  by_contra h
  have hf (v : V) (hv : (G.openGraph (ω ∪ J)).Reachable o v) :
      (G.cluster ω v).Finite := by
    apply Set.not_infinite.mp
    intro hi
    exact h ⟨v,hv,hi⟩
  have hσ (v : V) : (G.cluster ω v ∩ G.cluster (ω ∪ J) o).Finite := by
    by_cases hv : (G.openGraph (ω ∪ J)).Reachable o v
    · exact (hf v hv).inter_of_left _
    · have he : G.cluster ω v ∩ G.cluster (ω ∪ J) o = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx,hox⟩
        exact hv (hox.trans (G.cluster_mono Set.subset_union_left v hx).symm)
      rw [he]
      exact Set.finite_empty
  apply ho
  apply ((hf o (.refl _)).union (hJ.biUnion fun e _ =>
      (G.ends e).toFinset.finite_toSet.biUnion fun v _ => hσ v)).subset
  intro z hz
  rcases G.cluster_union_subset ω J o hz with hh | hh
  · exact Or.inl hh
  · obtain ⟨e,he,hh⟩ := Set.mem_iUnion₂.mp hh
    obtain ⟨v,hv,hvz⟩ := Set.mem_iUnion₂.mp hh
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr ⟨v,hv,hvz,hz⟩⟩)

lemma finite_bonds_connect_set (hc : G.fullGraph.Connected) (o : V)
    (S : Set V) (hS : S.Finite) :
    ∃ J : Set E, J.Finite ∧ ∀ s ∈ S, (G.openGraph J).Reachable o s := by
  obtain ⟨J,hJ,_,hconn⟩ := G.finite_subset_cluster_finite_witness hS
    (show S ⊆ G.cluster Set.univ o from fun s _ => hc o s)
  exact ⟨J,hJ,fun s hs => hconn hs⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_AutDisplacement
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma aut_moves_vertex_outside_ball [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (R : ℕ) :
    ∃ φ : G.Aut, φ.vertex o ∉ G.vertexBall o R := by
  obtain ⟨C,hC⟩ := G.orbit_density_radius hc hq o
  obtain ⟨v,hv⟩ := (G.vertexBall_finite hl o (R+C)).exists_notMem
  obtain ⟨φ,hφ⟩ := hC v
  refine ⟨φ,fun h => hv ?_⟩
  exact G.vertexBall_add h C (G.vertexBall_comm.mp hφ)

lemma aut_displaces_finite_bonds [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (S : Set E) (hS : S.Finite) :
    ∃ φ : G.Aut, Disjoint S (φ.edge '' S) := by
  obtain ⟨o⟩ := hc.nonempty
  obtain ⟨R,hR⟩ := G.finite_bonds_in_ball hc o hS
  obtain ⟨φ,hφ⟩ := G.aut_moves_vertex_outside_ball hc hl hq o (R+R)
  refine ⟨φ,(G.inducedEdges_disjoint (G.vertexBalls_disjoint hφ)).mono hR ?_⟩
  have hm := Aut.inducedEdges_map G φ hR
  rwa [Aut.vertexBall_image] at hm

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_CylinderApproximation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma finiteCoordinateEvents_ring : IsSetRing (finiteCoordinateEvents (E := E)) where
  empty_mem := ⟨∅,@MeasurableSet.empty (Set E) (blockSigma ((∅ : Finset E) : Set E))⟩
  union_mem := by
    rintro A B ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,?_⟩
    exact @MeasurableSet.union (Set E) (blockSigma ((S ∪ T : Finset E) : Set E)) _ _
      (blockSigma_mono (by simp) _ hS) (blockSigma_mono (by simp) _ hT)
  sdiff_mem := by
    rintro A B ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,?_⟩
    exact @MeasurableSet.diff (Set E) (blockSigma ((S ∪ T : Finset E) : Set E)) _ _
      (blockSigma_mono (by simp) _ hS) (blockSigma_mono (by simp) _ hT)

lemma generateFrom_finiteCoordinateEvents :
    MeasurableSpace.generateFrom (finiteCoordinateEvents (E := E)) =
      (Set.instMeasurableSpace : MeasurableSpace (Set E)) := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun A ⟨S,hS⟩ => blockSigma_le _ _ hS
  · change (⨆ e : E, coordinateSigma e) ≤ _
    refine iSup_le fun e => ?_
    intro A hA
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{e},?_⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Finset.mem_singleton_self e) le_rfl) :
      coordinateSigma e ≤ blockSigma (({e} : Finset E) : Set E)) _ hA

lemma exists_finiteCoordinate_approx (q : E → unitInterval)
    {A : Set (Set E)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (S : Finset E) (B : Set (Set E)), MeasurableSet[blockSigma (S : Set E)] B ∧
      law q (B ∆ A) < ε := by
  obtain ⟨B,⟨S,hB⟩,h⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    finiteCoordinateEvents_ring (μ := law q)
    (show ∃ D : Set (Set (Set E)), D.Countable ∧ D ⊆ finiteCoordinateEvents ∧
        law q (⋃₀ D)ᶜ = 0 from
      ⟨{Set.univ},by simp,by rintro A rfl; exact ⟨∅,@MeasurableSet.univ (Set E) (blockSigma ((∅ : Finset E) : Set E))⟩,by simp⟩)
    generateFrom_finiteCoordinateEvents.symm hA hε
  exact ⟨S,B,hB,h⟩

lemma measurable_image_equiv_blocks (e : E ≃ E) (S : Set E) :
    @Measurable (Set E) (Set E) (blockSigma (e.symm '' S)) (blockSigma S)
      (fun ω => e '' ω) := by
  apply measurable_iff_comap_le.mpr
  simp only [blockSigma, MeasurableSpace.comap_iSup]
  refine iSup₂_le fun x hx => ?_
  have hm : @Measurable (Set E) Prop (coordinateSigma (e.symm x)) inferInstance
      (fun ω => x ∈ e '' ω) := by
    have hh : (fun ω : Set E => x ∈ e '' ω) = (fun ω => e.symm x ∈ ω) := by
      funext ω
      exact propext (by simp)
    rw [hh]
    exact measurable_iff_comap_le.mpr le_rfl
  have hc := hm.comap_le
  rw [coordinateSigma,MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun ω : Set E => x ∈ e '' ω) inferInstance ≤ _
  exact hc.trans (le_iSup_of_le (e.symm x) (le_iSup_of_le ⟨x,hx,rfl⟩ le_rfl))

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BernoulliErgodicity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma invariant_zero_one (p : unitInterval) (ρ : I → E ≃ E)
    (hdisp : ∀ S : Finset E, ∃ i, Disjoint (S : Set E) ((ρ i).symm '' (S : Set E)))
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinv : ∀ i, (fun ω : Set E => ρ i '' ω) ⁻¹' A = A) :
    law (fun _ : E => p) A = 0 ∨ law (fun _ : E => p) A = 1 := by
  let μ := law (fun _ : E => p)
  have hsq : μ.real A ≤ (μ.real A)^2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hδ : 0 < ε/4 := by positivity
    obtain ⟨S,B,hB,happrox⟩ := exists_finiteCoordinate_approx (fun _ : E => p) hA
      (ENNReal.ofReal_pos.mpr hδ)
    have hBm : MeasurableSet B := blockSigma_le _ _ hB
    obtain ⟨i,hi⟩ := hdisp S
    let f : Set E → Set E := fun ω => ρ i '' ω
    let C := f ⁻¹' B
    have hf : Measurable f := measurable_image_equiv (ρ i)
    have hC : MeasurableSet[blockSigma ((ρ i).symm '' (S : Set E))] C :=
      (measurable_image_equiv_blocks (ρ i) (S : Set E)) hB
    have hCm : MeasurableSet C := hBm.preimage hf
    have hind : IndepSet B C μ :=
      (independent_disjoint_blocks (fun _ => p) (S : Set E) _ hi).indepSet_of_measurableSet hB hC
    have hpres (D : Set (Set E)) (hD : MeasurableSet D) : μ.real (f ⁻¹' D) = μ.real D := by
      change (μ (f ⁻¹' D)).toReal = (μ D).toReal
      rw [← Measure.map_apply hf hD]
      change ((law (fun _ : E => p)).map (fun ω => ρ i '' ω) D).toReal = _
      rw [law_map_equiv]
    have hCeq : μ.real C = μ.real B := hpres B hBm
    have hAB : μ.real (B ∆ A) ≤ ε/4 := by
      apply le_of_lt
      have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr happrox
      change (μ (B ∆ A)).toReal < ε/4
      rwa [ENNReal.toReal_ofReal hδ.le] at hh
    have hAC : μ.real (C ∆ A) ≤ ε/4 := by
      have he : C ∆ A = f ⁻¹' (B ∆ A) := by
        rw [Set.preimage_symmDiff,hinv]
      rw [he,hpres _ (hBm.symmDiff hA)]
      exact hAB
    have hcover : A ⊆ (B ∩ C) ∪ ((B ∆ A) ∪ (C ∆ A)) := by
      intro ω hω
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_symmDiff]
      tauto
    have hinter : μ.real (B ∩ C) = (μ.real B)^2 := by
      rw [measureReal_def,hind.measure_inter_eq_mul,ENNReal.toReal_mul]
      change μ.real B * μ.real C = _
      rw [hCeq,pow_two]
    have hbound : μ.real A ≤ (μ.real B)^2 + ε/2 := by
      have hh := (measureReal_mono hcover (μ := μ)).trans
        (measureReal_union_le (B ∩ C) ((B ∆ A) ∪ (C ∆ A)))
      have hu := measureReal_union_le (B ∆ A) (C ∆ A) (μ := μ)
      rw [hinter] at hh
      linarith
    have hdif : μ.real B - μ.real A ≤ ε/4 :=
      (le_abs_self _).trans ((abs_measureReal_sub_le_measureReal_symmDiff
        hBm.nullMeasurableSet hA.nullMeasurableSet).trans hAB)
    have hfac : (μ.real B - μ.real A)*(μ.real A + μ.real B) ≤ (ε/4)*2 := by
      apply (mul_le_mul_of_nonneg_right hdif (add_nonneg measureReal_nonneg measureReal_nonneg)).trans
      exact mul_le_mul_of_nonneg_left (by
        have ha := measureReal_le_one (μ := μ) (s := A)
        have hb := measureReal_le_one (μ := μ) (s := B)
        linarith) hδ.le
    nlinarith only [hbound,hfac]
  have ha0 : 0 ≤ μ.real A := measureReal_nonneg
  have ha1 : μ.real A ≤ 1 := measureReal_le_one
  have heq : μ.real A = 0 ∨ μ.real A = 1 := by
    have h : μ.real A * (μ.real A - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases heq with h | h
  · left
    exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (measure_ne_top μ A)
  · right
    exact (ENNReal.toReal_eq_one_iff _).mp h

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_GraphErgodicity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem invariant_event_zero_one [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (p : unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinv : ∀ φ : G.Aut, (fun ω : Set E => φ.edge '' ω) ⁻¹' A = A) :
    G.law p A = 0 ∨ G.law p A = 1 := by
  have hh := BernoulliProduct.invariant_zero_one p (fun φ : G.Aut => (Aut.symm G φ).edge)
    (fun S => by
      obtain ⟨φ,hφ⟩ := G.aut_displaces_finite_bonds hc hl hq (S : Set E) S.finite_toSet
      exact ⟨φ,hφ⟩) A hA (fun φ => hinv (Aut.symm G φ))
  simpa only [BernoulliProduct.law_const,law] using hh

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_CriticalClusterMultiplicity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infinitelyManyInfiniteClusters.exists_pairwise {ω : Set E}
    (h : G.infinitelyManyInfiniteClusters ω) (n : ℕ) :
    ∃ f : Fin n → V, (∀ i, (G.cluster ω (f i)).Infinite) ∧
      Pairwise (fun i j => ¬ (G.openGraph ω).Reachable (f i) (f j)) := by
  induction n with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨f,hf,hpair⟩ := ih
    obtain ⟨v,hv,hnew⟩ := h (Finset.univ.image f)
    refine ⟨Fin.cons v f,?_,?_⟩
    · intro i
      refine Fin.cases hv (fun j => ?_) i
      exact hf j
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun a => ?_) i
      · refine Fin.cases ?_ (fun b hij => ?_) j
        · exact fun hij => False.elim (hij rfl)
        · exact hnew (f b) (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩)
      · refine Fin.cases ?_ (fun b hij => ?_) j
        · exact fun _ hab => hnew (f a) (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) hab.symm
        · exact hpair (fun he => hij (congrArg Fin.succ he))

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_InvariantFiniteSets
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertex_aut_orbit_infinite [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (v : V) :
    (Set.range (fun φ : G.Aut => φ.vertex v)).Infinite := by
  intro hf
  obtain ⟨R,hR⟩ := G.finite_subset_vertexBall hc v hf
  obtain ⟨φ,hφ⟩ := G.aut_moves_vertex_outside_ball hc hl hq v R
  exact hφ (hR ⟨φ,rfl⟩)

lemma bounded_invariant_marks_null [Infinite V] [Countable V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (M : Set E → V → Prop)
    (hm : ∀ v, Measurable (fun ω => M ω v))
    (ha : ∀ (φ : G.Aut) ω v, M (φ.edge '' ω) (φ.vertex v) ↔ M ω v)
    (N : ℕ) (hb : ∀ ω, ∃ S : Finset V, S.card≤N ∧ ∀ v, M ω v → v∈S) (v : V) :
    G.law p {ω | M ω v}=0 := by
  have hmeas (x : V) : Measurable (fun ω => if M ω x then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite (hm x).setOf measurable_const
  have he (x : V) : (∫⁻ ω, if M ω x then (1:ℝ≥0∞) else 0 ∂G.law p) =
      G.law p {ω | M ω x} := by
    simpa only [Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
      (lintegral_indicator_one (μ := G.law p) (hm x).setOf)
  have hpoint (ω : Set E) : (∑' x, if M ω x then (1:ℝ≥0∞) else 0) ≤ N := by
    obtain ⟨S,hS,hcover⟩ := hb ω
    calc
      _ ≤ ∑' x, if x∈S then (1:ℝ≥0∞) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro x
        split_ifs with hx hs
        · rfl
        · exact False.elim (hs (hcover x hx))
        · exact zero_le
        · rfl
      _ = (S.card:ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun x hx => ite_eq_right hx)]
        simp
      _ ≤ N := by exact_mod_cast hS
  have hsum : (∑' x, G.law p {ω | M ω x}) ≤ N := by
    calc
      _ = ∫⁻ ω, ∑' x, if M ω x then (1:ℝ≥0∞) else 0 ∂G.law p := by
        rw [lintegral_tsum (fun x => (hmeas x).aemeasurable)]
        simp only [he]
      _ ≤ ∫⁻ _ : Set E, (N:ℝ≥0∞) ∂G.law p := lintegral_mono hpoint
      _ = N := by simp
  have hinv (φ : G.Aut) : G.law p {ω | M ω (φ.vertex v)} = G.law p {ω | M ω v} := by
    conv_lhs => rw [←G.law_map_aut p φ]
    rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge) (hm _).setOf]
    congr 1
    ext ω
    exact ha φ ω v
  by_contra hn
  have hf := ENNReal.finite_const_le_of_tsum_ne_top
    ((hsum.trans_lt (ENNReal.natCast_lt_top N)).ne) hn
  apply G.vertex_aut_orbit_infinite hc hl hq v
  apply hf.subset
  rintro x ⟨φ,rfl⟩
  change G.law p {ω | M ω v} ≤ G.law p {ω | M ω (φ.vertex v)}
  rw [hinv]

lemma measurable_vertexSetBound [Countable V] (A : Set E → Set V)
    (hm : ∀ v, Measurable (fun ω => v∈A ω)) (N : ℕ) :
    Measurable (G.vertexSetBound A N) := by
  exact .exists fun S : Finset V => measurable_const.and
    (.forall fun v => (hm v).imp measurable_const)

lemma vertexSetBound_aut (A : Set E → Set V)
    (ha : ∀ (φ : G.Aut) ω, A (φ.edge '' ω)=φ.vertex '' A ω)
    (N : ℕ) (φ : G.Aut) (ω : Set E) :
    G.vertexSetBound A N (φ.edge '' ω) ↔ G.vertexSetBound A N ω := by
  change (∃ S : Finset V, S.card≤N ∧ A (φ.edge '' ω)⊆S) ↔ _
  rw [ha]
  constructor
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex.symm,Finset.card_image_le.trans hS,?_⟩
    intro x hx
    exact Finset.mem_image.mpr ⟨φ.vertex x,h ⟨x,hx,rfl⟩,φ.vertex.symm_apply_apply x⟩
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex,Finset.card_image_le.trans hS,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact Finset.mem_image.mpr ⟨x,h hx,rfl⟩

theorem invariant_finite_vertex_set_empty_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (A : Set E → Set V)
    (hm : ∀ v, Measurable (fun ω => v∈A ω))
    (ha : ∀ (φ : G.Aut) ω, A (φ.edge '' ω)=φ.vertex '' A ω) :
    ∀ᵐ ω ∂G.law p, (A ω).Finite → A ω=∅ := by
  let := G.countable_vertices hc hl
  have hn (N : ℕ) (v : V) : ∀ᵐ ω ∂G.law p, ¬(G.vertexSetBound A N ω ∧ v∈A ω) := by
    rw [ae_iff]
    simp only [not_not]
    apply G.bounded_invariant_marks_null hc hl hq p
      (fun ω v => G.vertexSetBound A N ω ∧ v∈A ω)
      (fun v => (G.measurable_vertexSetBound A hm N).and (hm v))
      (fun φ ω v => by
        rw [G.vertexSetBound_aut A ha N φ ω,ha]
        simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]) N
    intro ω
    by_cases hh : G.vertexSetBound A N ω
    · obtain ⟨S,hS,hcover⟩ := hh
      exact ⟨S,hS,fun x hx => hcover hx.2⟩
    · exact ⟨∅,Nat.zero_le N,fun x hx => (hh hx.1).elim⟩
  have hall : ∀ᵐ ω ∂G.law p, ∀ N : ℕ, ∀ v : V,
      ¬(G.vertexSetBound A N ω ∧ v∈A ω) :=
    ae_all_iff.mpr (fun N => ae_all_iff.mpr (hn N))
  filter_upwards [hall] with ω hω hf
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact hω hf.toFinset.card v ⟨⟨hf.toFinset,le_rfl,fun _ hx => hf.mem_toFinset.mpr hx⟩,hv⟩

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

lemma stabilizerWeight_ne_top (o x : V) : G.stabilizerWeight o x ≠ ∞ :=
  ENNReal.ofReal_ne_top

lemma stabilizerWeight_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : 0 < G.stabilizerWeight o x :=
  ENNReal.ofReal_pos.mpr (G.modularRatio_pos hc hl x o)

@[simp] lemma stabilizerWeight_self (o : V) : G.stabilizerWeight o o = 1 := by
  simp [stabilizerWeight,modularRatio_self]

lemma stabilizerWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight o x =
      G.stabilizerWeight o a * G.stabilizerWeight a x := by
  unfold stabilizerWeight
  rw [←ENNReal.ofReal_mul (G.modularRatio_pos hc hl a o).le]
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

lemma modularMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S =
      G.stabilizerWeight o a * G.modularMass a S := by
  unfold modularMass
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  split_ifs with hx
  · exact G.stabilizerWeight_change_base hc hl o a x
  · exact (mul_zero _).symm

lemma modularMass_eq_top_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S = ∞ ↔ G.modularMass a S = ∞ := by
  rw [G.modularMass_change_base hc hl o a S,ENNReal.mul_eq_top]
  simp [G.stabilizerWeight_ne_top o a,(G.stabilizerWeight_pos hc hl o a).ne']

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

lemma Aut.modularMass_image (φ : G.Aut) (o : V) (S : Set V) :
    G.modularMass (φ.vertex o) (φ.vertex '' S) = G.modularMass o S := by
  unfold modularMass
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro x
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,Aut.stabilizerWeight]

lemma measurable_modularClusterMass [Countable V] [Countable E] (o v : V) :
    Measurable (fun ω : Set E => G.modularMass o (G.cluster ω v)) := by
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (G.measurable_reachable v x).setOf measurable_const

lemma measurableSet_lightInfiniteEvent [Countable V] [Countable E] (o v : V) :
    MeasurableSet (G.lightInfiniteEvent o v) := by
  exact (G.measurable_infinite_cluster v).setOf.inter
    (measurableSet_lt (G.measurable_modularClusterMass o v) measurable_const)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakClusters
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.clusterPeak_iff (φ : G.Aut) (ω : Set E) (x : V) :
    G.clusterPeak (φ.edge '' ω) (φ.vertex x) ↔ G.clusterPeak ω x := by
  unfold clusterPeak
  constructor
  · intro h z hz
    have hr : (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex x) (φ.vertex z) :=
      (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mpr hz
    simpa only [Aut.stabilizerWeight] using h (φ.vertex z) hr
  · intro h z hz
    obtain ⟨y,rfl⟩ := φ.vertex.surjective z
    rw [Aut.stabilizerWeight]
    exact h y ((SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mp hz)

lemma measurable_clusterPeak [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeak ω x) := by
  exact .forall (fun z => (G.measurable_reachable x z).imp measurable_const)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularSuperlevels
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_le_one_iff (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight a x ≤ 1 ↔ G.stabilizerWeight o x ≤ G.stabilizerWeight o a := by
  rw [G.stabilizerWeight_change_base hc hl o a x]
  conv_rhs => rhs; rw [←mul_one (G.stabilizerWeight o a)]
  exact (ENNReal.mul_le_mul_iff_right (G.stabilizerWeight_pos hc hl o a).ne'
    (G.stabilizerWeight_ne_top o a)).symm

lemma mem_clusterUpperSet_self (ω : Set E) (v : V) : v∈G.clusterUpperSet ω v := by
  exact ⟨SimpleGraph.Reachable.refl v,by simp⟩

lemma finite_clusterUpperSet_of_mass_ne_top {ω : Set E} {v : V}
    (hm : G.modularMass v (G.cluster ω v) ≠ ∞) : (G.clusterUpperSet ω v).Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm (ε := 1) one_ne_zero).subset
  intro x hx
  change 1 ≤ if x∈G.cluster ω v then G.stabilizerWeight v x else 0
  rw [ite_eq_left hx.1]
  exact hx.2

lemma finite_clusterUpperSet_has_peak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hf : (G.clusterUpperSet ω v).Finite) :
    ∃ y∈G.cluster ω v, G.clusterPeak ω y ∧
      G.peakBound hf.toFinset.card ω y := by
  obtain ⟨y,hy,hmax⟩ := hf.toFinset.exists_max_image (G.stabilizerWeight v)
    ⟨v,hf.mem_toFinset.mpr (G.mem_clusterUpperSet_self ω v)⟩
  have hy' := hf.mem_toFinset.mp hy
  have hbound (z : V) (hz : z∈G.cluster ω v) : G.stabilizerWeight v z ≤ G.stabilizerWeight v y := by
    by_cases h : 1≤G.stabilizerWeight v z
    · exact hmax z (hf.mem_toFinset.mpr ⟨hz,h⟩)
    · exact (le_of_not_ge h).trans hy'.2
  have hpeak : G.clusterPeak ω y := by
    intro z hz
    exact (G.stabilizerWeight_le_one_iff hc hl v y z).mpr (hbound z (hy'.1.trans hz))
  refine ⟨y,hy'.1,hpeak,hf.toFinset,le_rfl,?_⟩
  intro z hz
  apply hf.mem_toFinset.mpr
  refine ⟨hy'.1.trans hz.1,?_⟩
  exact hy'.2.trans ((G.stabilizerWeight_le_one_iff hc hl v z y).mp (hz.2 y hz.1.symm))

lemma clusterPeaks_finite_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hm : G.modularMass v (G.cluster ω v) ≠ ∞) :
    (G.clusterPeaks ω v).Finite := by
  apply (G.finite_clusterUpperSet_of_mass_ne_top hm).subset
  intro x hx
  refine ⟨hx.1,?_⟩
  have hh := (G.stabilizerWeight_le_one_iff hc hl v x v).mp (hx.2 v hx.1.symm)
  simpa only [G.stabilizerWeight_self] using hh

lemma clusterPeaks_nonempty_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hm : G.modularMass v (G.cluster ω v) ≠ ∞) :
    (G.clusterPeaks ω v).Nonempty := by
  obtain ⟨y,hy,hp,_⟩ := G.finite_clusterUpperSet_has_peak hc hl ω v
    (G.finite_clusterUpperSet_of_mass_ne_top hm)
  exact ⟨y,hy,hp⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EncounterGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_separatedInfiniteTupleEvent [Countable V] [Countable E]
    {k : ℕ} (v : Fin k → V) : MeasurableSet (G.separatedInfiniteTupleEvent v) := by
  exact ((Measurable.forall fun i => G.measurable_infinite_cluster (v i)).and
    (Measurable.forall fun i => Measurable.forall fun j =>
      measurable_const.imp (G.measurable_reachable (v i) (v j)).not)).setOf

lemma measurableSet_encounterEvent [Countable V] [Countable E]
    (J : Set E) (o : V) (k : ℕ) : MeasurableSet (G.encounterEvent J o k) := by
  have hm : Measurable (fun ω : Set E => ω\J) := by
    exact Measurable.of_eval (fun edge => (measurable_set_mem edge).and measurable_const)
  exact (Measurable.exists fun v : Fin k → V =>
    (Measurable.forall fun i => G.measurable_reachable o (v i)).and
    ((Measurable.forall fun i => (G.measurable_infinite_cluster (v i)).comp hm).and
      (Measurable.forall fun i => Measurable.forall fun j =>
        measurable_const.imp ((G.measurable_reachable (v i) (v j)).comp hm).not))).setOf

lemma infinite_cluster_sdiff_has_infinite (ω J : Set E) (hJ : J.Finite) (v : V)
    (hv : (G.cluster ω v).Infinite) :
    ∃ w, (G.openGraph ω).Reachable v w ∧ (G.cluster (ω\J) w).Infinite := by
  have hsub : ω⊆(ω\J)∪(ω∩J) := by
    intro e he
    by_cases h : e∈J
    · exact Or.inr ⟨he,h⟩
    · exact Or.inl ⟨he,h⟩
  obtain ⟨w,hw,hi⟩ := G.infinite_cluster_union_has_old (ω\J) (ω∩J)
    (hJ.inter_of_right _) v (hv.mono (G.cluster_mono hsub v))
  exact ⟨w,G.cluster_mono (by intro e h; rcases h with h|h; exact h.1; exact h.1) v hw,hi⟩

lemma separatedTuple_force_encounter {k : ℕ} (v : Fin k → V)
    (J : Set E) (hJ : J.Finite) (o : V)
    (hconn : ∀ i, (G.openGraph J).Reachable o (v i))
    (ω : Set E) (hω : ω∈G.separatedInfiniteTupleEvent v) :
    J∪ω∈G.encounterEvent J o k := by
  have h (i : Fin k) := G.infinite_cluster_sdiff_has_infinite ω J hJ (v i) (hω.1 i)
  choose w hw hi using h
  refine ⟨w,?_,?_,?_⟩
  · intro i
    exact (G.cluster_mono Set.subset_union_left o (hconn i)).trans
      (G.cluster_mono Set.subset_union_right (v i) (hw i))
  · simpa only [Set.union_sdiff_left] using hi
  · intro i j hij hpath
    have hpath' : (G.openGraph ω).Reachable (w i) (w j) := by
      apply G.cluster_mono (show (J∪ω)\J⊆ω from fun _ h => by
        rcases h.1 with hh|hh
        · exact False.elim (h.2 hh)
        · exact hh) (w i) hpath
    exact hω.2 hij ((hw i).trans (hpath'.trans (hw j).symm))

lemma exists_positive_separatedTuple [Countable V] [Countable E]
    (p : unitInterval) (k : ℕ)
    (hm : ∀ᵐ ω ∂G.law p, G.infinitelyManyInfiniteClusters ω) :
    ∃ v : Fin k → V, 0<G.law p (G.separatedInfiniteTupleEvent v) := by
  by_contra h
  have hall : ∀ v : Fin k → V, G.law p (G.separatedInfiniteTupleEvent v)=0 := by
    intro v
    exact le_antisymm (le_of_not_gt (fun hv => h ⟨v,hv⟩)) bot_le
  have hn : G.law p (⋃ v : Fin k → V, G.separatedInfiniteTupleEvent v)=0 :=
    measure_iUnion_null hall
  have he : ∀ᵐ ω ∂G.law p, ω∈⋃ v : Fin k → V, G.separatedInfiniteTupleEvent v := by
    filter_upwards [hm] with ω hω
    obtain ⟨v,hv⟩ := hω.exists_pairwise G k
    exact Set.mem_iUnion.mpr ⟨v,hv⟩
  have ho := (ae_iff_prob_eq_one (MeasurableSet.iUnion
    (fun v => G.measurableSet_separatedInfiniteTupleEvent v)).mem).mp he
  exact zero_ne_one (hn.symm.trans ho)

theorem exists_positive_encounter [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : 0<p) (o : V) (k : ℕ)
    (hm : ∀ᵐ ω ∂G.law p, G.infinitelyManyInfiniteClusters ω) :
    ∃ J : Set E, J.Finite ∧ 0<G.law p (G.encounterEvent J o k) := by
  obtain ⟨v,hv⟩ := G.exists_positive_separatedTuple p k hm
  obtain ⟨J,hJ,hconn⟩ := G.finite_bonds_connect_set hc o (Set.range v) (Set.finite_range v)
  refine ⟨J,hJ,?_⟩
  by_contra h
  have hz : G.law p (G.encounterEvent J o k)=0 := le_antisymm (le_of_not_gt h) bot_le
  have hn := BernoulliProduct.finite_union_preimage_null (fun _ : E => p) (fun _ => hp)
    J hJ (G.encounterEvent J o k) (G.measurableSet_encounterEvent J o k)
    (by simpa only [BernoulliProduct.law_const,law] using hz)
  have hn' : G.law p ((fun ω : Set E => J∪ω) ⁻¹' G.encounterEvent J o k)=0 := by
    simpa only [BernoulliProduct.law_const,law] using hn
  have hsub : G.separatedInfiniteTupleEvent v ⊆
      (fun ω : Set E => J∪ω) ⁻¹' G.encounterEvent J o k := by
    intro ω hω
    exact G.separatedTuple_force_encounter v J hJ o (fun i => hconn (v i) ⟨i,rfl⟩) ω hω
  exact hv.ne' (measure_mono_null hsub hn')

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_LightClusterNumber
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma lightInfiniteEvent_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a v : V) : G.lightInfiniteEvent o v=G.lightInfiniteEvent a v := by
  ext ω
  change (_ ∧ _<∞) ↔ (_ ∧ _<∞)
  simp only [lt_top_iff_ne_top]
  exact and_congr Iff.rfl (not_congr (G.modularMass_eq_top_change_base hc hl o a _))

lemma lightInfiniteEvent_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {ω : Set E} {v x : V} (hx : (G.openGraph ω).Reachable v x)
    (hv : ω∈G.lightInfiniteEvent v v) : ω∈G.lightInfiniteEvent x x := by
  change (G.cluster ω x).Infinite ∧ G.modularMass x (G.cluster ω x)<∞
  have he := G.cluster_eq_of_reachable hx
  rw [←he]
  refine ⟨hv.1,?_⟩
  rw [lt_top_iff_ne_top]
  intro h
  exact hv.2.ne ((G.modularMass_eq_top_change_base hc hl v x _).mpr h)

lemma Aut.lightInfiniteEvent_self_iff (φ : G.Aut) (ω : Set E) (v : V) :
    φ.edge '' ω∈G.lightInfiniteEvent (φ.vertex v) (φ.vertex v) ↔
      ω∈G.lightInfiniteEvent v v := by
  change (_ ∧ _<∞) ↔ (_ ∧ _<∞)
  rw [←φ.cluster_image,φ.modularMass_image]
  exact and_congr (Set.infinite_image_iff φ.vertex.injective.injOn) Iff.rfl

lemma measurable_lightInfinitePeaks [Countable V] [Countable E] (v : V) :
    Measurable (fun ω => v∈G.lightInfinitePeaks ω) :=
  (G.measurableSet_lightInfiniteEvent v v).mem.and (G.measurable_clusterPeak v)

lemma lightInfinitePeaks_aut (φ : G.Aut) (ω : Set E) :
    G.lightInfinitePeaks (φ.edge '' ω)=φ.vertex '' G.lightInfinitePeaks ω := by
  ext y
  obtain ⟨v,rfl⟩ := φ.vertex.surjective y
  simp only [lightInfinitePeaks,Set.mem_ofPred_eq,φ.lightInfiniteEvent_self_iff,
    φ.clusterPeak_iff,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

lemma lightInfinitePeaks_finite_of_cover (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (S : Set V) (hS : S.Finite) (hcover : G.lightClusterCover ω S) :
    (G.lightInfinitePeaks ω).Finite := by
  let T := {s∈S | ω∈G.lightInfiniteEvent s s}
  have hT : T.Finite := hS.subset (fun _ hx => hx.1)
  refine (hT.biUnion (fun s hs => G.clusterPeaks_finite_of_mass_ne_top hc hl ω s hs.2.2.ne)).subset ?_
  intro v hv
  obtain ⟨s,hs,hvs⟩ := hcover v hv.1
  exact Set.mem_iUnion₂.mpr ⟨s,⟨hs,G.lightInfiniteEvent_of_reachable hc hl hvs hv.1⟩,hvs.symm,hv.2⟩

lemma lightInfinitePeaks_nonempty (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hv : ω∈G.lightInfiniteEvent v v) :
    (G.lightInfinitePeaks ω).Nonempty := by
  obtain ⟨x,hx,hpeak⟩ := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω v hv.2.ne
  exact ⟨x,G.lightInfiniteEvent_of_reachable hc hl hx hv,hpeak⟩

lemma infinitelyManyLightClusters_iff_no_finite_cover (ω : Set E) :
    G.infinitelyManyLightClusters ω ↔ ∀ S : Finset V, ¬G.lightClusterCover ω (S : Set V) := by
  simp only [infinitelyManyLightClusters,lightClusterCover]
  push Not
  rfl

theorem light_zero_or_infinitely_many_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    ∀ᵐ ω ∂G.law p, (∃ v, ω∈G.lightInfiniteEvent v v) → G.infinitelyManyLightClusters ω := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hh := G.invariant_finite_vertex_set_empty_ae hc hl hq p G.lightInfinitePeaks
    G.measurable_lightInfinitePeaks G.lightInfinitePeaks_aut
  filter_upwards [hh] with ω hω ⟨v,hv⟩
  rw [G.infinitelyManyLightClusters_iff_no_finite_cover]
  intro S hS
  have hf := G.lightInfinitePeaks_finite_of_cover hc hl ω (S : Set V) S.finite_toSet hS
  have hn := G.lightInfinitePeaks_nonempty hc hl ω v hv
  rw [hω hf] at hn
  exact Set.not_nonempty_empty hn

lemma light_exists_invariant (φ : G.Aut) (ω : Set E) :
    (∃ v, φ.edge '' ω∈G.lightInfiniteEvent v v) ↔ ∃ v, ω∈G.lightInfiniteEvent v v := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨x,rfl⟩ := φ.vertex.surjective v
    exact ⟨x,(φ.lightInfiniteEvent_self_iff G ω x).mp hv⟩
  · rintro ⟨v,hv⟩
    exact ⟨φ.vertex v,(φ.lightInfiniteEvent_self_iff G ω v).mpr hv⟩

theorem infinitely_many_light_ae_of_positive [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (o v : V) (hv : 0<G.law p (G.lightInfiniteEvent o v)) :
    ∀ᵐ ω ∂G.law p, G.infinitelyManyLightClusters ω := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hm : MeasurableSet {ω | ∃ v, ω∈G.lightInfiniteEvent v v} :=
    (Measurable.exists fun v => (G.measurableSet_lightInfiniteEvent v v).mem).setOf
  have hpos : 0<G.law p {ω | ∃ v, ω∈G.lightInfiniteEvent v v} := by
    apply hv.trans_le
    apply measure_mono
    intro ω hω
    refine ⟨v,?_⟩
    rwa [G.lightInfiniteEvent_change_base hc hl o v v] at hω
  have hone : G.law p {ω | ∃ v, ω∈G.lightInfiniteEvent v v}=1 := by
    rcases G.invariant_event_zero_one hc hl hq p _ hm
      (fun φ => Set.ext fun ω => G.light_exists_invariant φ ω) with hz|ho
    · exact False.elim (hpos.ne' hz)
    · exact ho
  have hex : ∀ᵐ ω ∂G.law p, ∃ v, ω∈G.lightInfiniteEvent v v := by
    exact (ae_iff_prob_eq_one hm.mem).mpr hone
  filter_upwards [G.light_zero_or_infinitely_many_ae hc hl hq p,hex] with ω hω hh
  exact hω hh

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_MainInfiniteLightBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_infinite_light_or_sparse_boundary [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (o : V)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    (¬G.CombinatoriallyUnimodular ∧
      (∀ᵐ ω ∂G.law G.criticalProbability, G.infinitelyManyLightClusters ω) ∧
      (∀ᵐ ω ∂G.law G.criticalProbability, ω∈G.atMostOneHeavy o)) ∨
    (G.SubexponentialGrowth ∧ ∃ d : ℕ, 2≤d ∧
      ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) := by
  rcases G.main_light_or_sparse_polynomial_boundary_bs hc hl hq hpc o hper with ⟨hu,v,hv⟩|hpoly
  · exact Or.inl ⟨hu,G.infinitely_many_light_ae_of_positive hc hl hq G.criticalProbability o v hv,
      G.atMostOneHeavy_critical_ae_bs hc hl hq hpc o⟩
  · exact Or.inr hpoly

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_MainAllLightBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infinitelyManyLightClusters.infinite {ω : Set E}
    (h : G.infinitelyManyLightClusters ω) : G.infinitelyManyInfiniteClusters ω := by
  intro S
  obtain ⟨v,hv,hs⟩ := h S
  exact ⟨v,hv.1,hs⟩

theorem main_all_light_or_sparse_boundary [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (o : V)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    (¬G.CombinatoriallyUnimodular ∧
      (∀ᵐ ω ∂G.law G.criticalProbability, G.infinitelyManyLightClusters ω ∧
        ∀ v, G.modularMass o (G.cluster ω v)<∞) ∧
      (∀ ε : ℝ, 0<ε → ∃ R : ℕ, ∀ x y, y∉G.vertexBall x R →
        CriticalPercolation.Sharpness.twoPoint G G.criticalProbability x y<ε) ∧
      (∀ k : ℕ, ∃ J : Set E, J.Finite ∧
        0<G.law G.criticalProbability (G.encounterEvent J o k))) ∨
    (G.SubexponentialGrowth ∧ ∃ d : ℕ, 2≤d ∧
      ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  rcases G.main_infinite_light_or_sparse_boundary hc hl hq hpc o hper with
    ⟨hu,hlight,_⟩|hpoly
  · have hp : 0<G.criticalProbability := by
      by_contra hn
      have he : G.criticalProbability=0 := le_antisymm (le_of_not_gt hn) bot_le
      exact hper (by rw [he,G.law_zero_percolates])
    refine Or.inl ⟨hu,hlight.and (G.nonunimodular_critical_mass_finite_ae_bs hc hl hq hpc hu o),
      G.nonunimodular_critical_twoPoint_decay_bs hc hl hq hpc hu,?_⟩
    intro k
    exact G.exists_positive_encounter hc G.criticalProbability hp o k
      (hlight.mono (fun _ h => h.infinite G))
  · exact Or.inr hpoly

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_MainSparseBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_sparse_polynomial [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    G.SubexponentialGrowth ∧ G.CombinatoriallyUnimodular ∧
      ∃ d : ℕ, 2≤d ∧ ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d := by
  have hu : G.CombinatoriallyUnimodular := by
    by_contra hn
    exact hper (G.nonunimodular_no_percolation_at_criticality_bs hc hl hq hn hpc)
  obtain ⟨o⟩ := hc.nonempty
  rcases G.main_all_light_or_sparse_boundary hc hl hq hpc o hper with ⟨hn,_⟩|⟨hg,hpoly⟩
  · exact False.elim (hn hu)
  · exact ⟨hg,hu,hpoly⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphAutomorphismTopology
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

lemma continuous_variable_eval : Continuous (fun p : (X → X) × X => p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr fun x => continuous_apply x

variable (Γ : SimpleGraph X)

attribute [local instance] OAI.CriticalPercolation.GraphTopology.instTopologicalSpaceIso_solutions
omit [DiscreteTopology X] in
lemma coordinates_embedding : IsEmbedding (coordinates Γ) where
  eq_induced := rfl
  injective := by
    intro g h he
    apply RelIso.ext
    intro x
    exact congrFun (congrArg Prod.fst he) x

omit [DiscreteTopology X] in
lemma continuous_eval (x : X) : Continuous (fun g : Γ ≃g Γ => g x) :=
  (continuous_apply x).comp (continuous_fst.comp (coordinates_embedding Γ).continuous)

omit [TopologicalSpace X] [DiscreteTopology X] in
lemma coordinates_range : Set.range (coordinates Γ) =
    {p : (X → X) × (X → X) |
      (∀ x, p.2 (p.1 x)=x) ∧ (∀ x, p.1 (p.2 x)=x) ∧
      (∀ x y, Γ.Adj (p.1 x) (p.1 y) ↔ Γ.Adj x y)} := by
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g.symm_apply_apply,g.apply_symm_apply,fun _ _ => g.map_adj_iff⟩
  · rintro ⟨hleft,hright,hadj⟩
    refine ⟨{toEquiv := ⟨p.1,p.2,hleft,hright⟩,map_rel_iff' := fun {x y} => hadj x y},?_⟩
    exact Prod.eta p

lemma coordinates_closed : IsClosed (Set.range (coordinates Γ)) := by
  rw [coordinates_range]
  simp only [Set.ofPred_and,Set.ofPred_forall]
  refine (isClosed_iInter fun x => ?_).inter ((isClosed_iInter fun x => ?_).inter
    (isClosed_iInter fun x => isClosed_iInter fun y => ?_))
  · change IsClosed {p : (X → X) × (X → X) | p.2 (p.1 x)=x}
    exact isClosed_eq ((continuous_variable_eval (X := X)).comp (continuous_snd.prodMk
      ((continuous_apply x).comp continuous_fst))) continuous_const
  · change IsClosed {p : (X → X) × (X → X) | p.1 (p.2 x)=x}
    exact isClosed_eq ((continuous_variable_eval (X := X)).comp (continuous_fst.prodMk
      ((continuous_apply x).comp continuous_snd))) continuous_const
  · change IsClosed {p : (X → X) × (X → X) | Γ.Adj (p.1 x) (p.1 y) ↔ Γ.Adj x y}
    exact (isClosed_discrete {p : X × X | Γ.Adj p.1 p.2 ↔ Γ.Adj x y}).preimage
      (show Continuous (fun p : (X → X) × (X → X) => (p.1 x,p.1 y)) from
        ((continuous_apply x).comp continuous_fst).prodMk
          ((continuous_apply y).comp continuous_fst))

lemma coordinates_closedEmbedding : IsClosedEmbedding (coordinates Γ) :=
  ⟨coordinates_embedding Γ,coordinates_closed Γ⟩

instance aut_t2 : T2Space (Γ ≃g Γ) := (coordinates_embedding Γ).t2Space

lemma compact_coordinate_bounds (F : X → Set X) (hF : ∀ x, (F x).Finite) :
    IsCompact {g : Γ ≃g Γ | (∀ x, g x∈F x) ∧ (∀ x, g.symm x∈F x)} := by
  have hK : IsCompact {f : X → X | ∀ x, f x∈F x} :=
    isCompact_pi_infinite fun x => (hF x).isCompact
  exact (coordinates_closedEmbedding Γ).isCompact_preimage (hK.prod hK)

lemma isClosed_eval_mem (x : X) (S : Set X) :
    IsClosed {g : Γ ≃g Γ | g x∈S} :=
  (isClosed_discrete S).preimage (continuous_eval Γ x)

lemma isOpen_eval_mem (x : X) (S : Set X) :
    IsOpen {g : Γ ≃g Γ | g x∈S} :=
  (isOpen_discrete S).preimage (continuous_eval Γ x)

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma reachBall_self (o : X) (r : ℕ) : o∈reachBall Γ o r :=
  ⟨SimpleGraph.Walk.nil,Nat.zero_le _⟩

lemma reachBall_symm {o x : X} {r : ℕ} (h : x∈reachBall Γ o r) :
    o∈reachBall Γ x r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.reverse,by simpa using hp⟩

lemma inverse_displacement {o : X} {r : ℕ} (g : Γ ≃g Γ)
    (h : g o∈reachBall Γ o r) : g.symm o∈reachBall Γ o r := by
  have hh := reachBall_symm Γ (iso_reachBall Γ g.symm h)
  simpa using hh

variable [TopologicalSpace X] [DiscreteTopology X]

attribute [local instance] OAI.CriticalPercolation.GraphTopology.instTopologicalSpaceIso_solutions_1
lemma compact_displacement (hc : Γ.Connected)
    (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (r : ℕ) :
    IsCompact {g : Γ ≃g Γ | g o∈reachBall Γ o r} := by
  have hp : ∀ x, ∃ p : Γ.Walk o x, True := fun x => by
    obtain ⟨p⟩ := hc o x
    exact ⟨p,trivial⟩
  choose p _ using hp
  let F : X → Set X := fun x => reachBall Γ o (r+(p x).length)
  have hfb : ∀ (g : Γ ≃g Γ), g o∈reachBall Γ o r → ∀ x, g x∈F x := by
    intro g hg x
    exact reachBall_add Γ hg (iso_reachBall Γ g ⟨p x,le_rfl⟩)
  apply (compact_coordinate_bounds Γ F (fun x => reachBall_finite Γ hl o _)).of_isClosed_subset
    (isClosed_eval_mem Γ o _)
  intro g hg
  exact ⟨hfb g hg,hfb g.symm (inverse_displacement Γ g hg)⟩

lemma open_displacement (o : X) (r : ℕ) :
    IsOpen {g : Γ ≃g Γ | g o∈reachBall Γ o r} := isOpen_eval_mem Γ o _

instance aut_totallyDisconnected : TotallyDisconnectedSpace (Γ ≃g Γ) :=
  (coordinates_embedding Γ).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphApproximateNeighborhoods
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma iso_reachBall_image (g : Γ ≃g Γ) (o : X) (r : ℕ) :
    g '' reachBall Γ o r=reachBall Γ (g o) r := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact iso_reachBall Γ g hy
  · intro x hx
    refine ⟨g.symm x,?_,g.apply_symm_apply x⟩
    simpa using iso_reachBall Γ g.symm hx

lemma reachBall_ncard_eq (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o x : X) (r : ℕ) :
    (reachBall Γ x r).ncard=(reachBall Γ o r).ncard := by
  obtain ⟨g,rfl⟩ := ht o x
  rw [←iso_reachBall_image Γ g o r,Set.ncard_image_of_injective _ g.injective]

lemma one_mem_displacement (o : X) (r : ℕ) : 1∈displacement Γ o r :=
  reachBall_self Γ o r

lemma displacement_inv {o : X} {r : ℕ} {g : Γ ≃g Γ} :
    g⁻¹∈displacement Γ o r ↔ g∈displacement Γ o r := by
  constructor
  · intro h
    change g o∈reachBall Γ o r
    simpa using inverse_displacement Γ g.symm h
  · exact inverse_displacement Γ g

lemma displacement_mul_subset (o : X) (r s : ℕ) :
    displacement Γ o r * displacement Γ o s ⊆ displacement Γ o (r+s) := by
  rintro g ⟨a,ha,b,hb,rfl⟩
  exact reachBall_add Γ ha (iso_reachBall Γ a hb)

lemma reachBall_packing (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    ∃ F : Finset X, (↑F : Set X)⊆reachBall Γ o (4*r) ∧ F.card≤K ∧
      ∀ u∈reachBall Γ o (4*r), ∃ v∈F, u∈reachBall Γ v (2*r) := by
  let A := (reachBall_finite Γ hl o (4*r)).toFinset
  let C : Finset (Finset X) := A.powerset.filter
    (fun F => (F : Set X).PairwiseDisjoint (fun v => reachBall Γ v r))
  obtain ⟨F,hFmax⟩ := C.exists_maximal <| Finset.filter_nonempty_iff.mpr
    ⟨∅,Finset.empty_mem_powerset _,by simp⟩
  simp only [C,Finset.mem_filter,Finset.mem_powerset] at hFmax
  obtain ⟨hFA,hF⟩ := hFmax.1
  have hFo : (F : Set X)⊆reachBall Γ o (4*r) := by
    intro u hu
    exact (reachBall_finite Γ hl o (4*r)).mem_toFinset.mp (hFA hu)
  have hsub : (⋃ u∈(F : Set X), reachBall Γ u r) ⊆ reachBall Γ o (5*r) := by
    intro v hv
    obtain ⟨u,hu,hv⟩ := Set.mem_iUnion₂.mp hv
    simpa only [show 4*r+r=5*r by omega] using reachBall_add Γ (hFo hu) hv
  have hcount : F.card*(reachBall Γ o r).ncard≤(reachBall Γ o (5*r)).ncard := by
    calc
      F.card*(reachBall Γ o r).ncard = ∑ u∈F, (reachBall Γ u r).ncard := by
        symm
        apply Finset.sum_const_nat
        intro u _
        exact reachBall_ncard_eq Γ ht o u r
      _ = (⋃ u∈(F : Set X), reachBall Γ u r).ncard := by
        rw [(F.finite_toSet).ncard_biUnion (fun u _ => reachBall_finite Γ hl u r) hF,
          finsum_mem_coe_finset]
      _ ≤ (reachBall Γ o (5*r)).ncard := Set.ncard_le_ncard hsub (reachBall_finite Γ hl o _)
  have hpos : 0<(reachBall Γ o r).ncard :=
    (Set.ncard_pos (reachBall_finite Γ hl o r)).mpr ⟨o,reachBall_self Γ o r⟩
  refine ⟨F,hFo,le_of_mul_le_mul_right (hcount.trans hd) hpos,?_⟩
  intro u hu
  by_cases huF : u∈F
  · exact ⟨u,huF,reachBall_self Γ u _⟩
  by_cases! H : ∀ v∈F, Disjoint (reachBall Γ u r) (reachBall Γ v r)
  · refine False.elim (hFmax.not_gt ?_ (Finset.ssubset_insert huF))
    rw [Finset.insert_subset_iff,Finset.coe_insert]
    exact ⟨⟨(reachBall_finite Γ hl o (4*r)).mem_toFinset.mpr hu,hFA⟩,
      hF.insert (fun v hv _ => H v hv)⟩
  · simp_rw [Set.not_disjoint_iff] at H
    obtain ⟨v,hv,w,hwu,hwv⟩ := H
    refine ⟨v,hv,?_⟩
    simpa only [show r+r=2*r by omega] using
      reachBall_add Γ hwv (reachBall_symm Γ hwu)

lemma displacement_cover_of_doubling (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    CovBySMul (Γ ≃g Γ) (K : ℝ) (displacement Γ o (4*r)) (displacement Γ o (2*r)) := by
  obtain ⟨F,hFo,hFK,hcover⟩ := reachBall_packing Γ hl ht o r K hd
  have hex : ∀ v : F, ∃ φ : Γ ≃g Γ, φ o=v.val := fun v => ht o v.val
  choose φ hφ using hex
  let H := Finset.univ.image φ
  have hH : H.card≤K := (Finset.card_image_le).trans (by simpa using hFK)
  refine ⟨H,by exact_mod_cast hH,?_⟩
  intro ψ hψ
  obtain ⟨v,hv,huv⟩ := hcover (ψ o) hψ
  let c := φ ⟨v,hv⟩
  have hc : c∈H := Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  have hco : c o=v := hφ ⟨v,hv⟩
  have hrem : c⁻¹*ψ∈displacement Γ o (2*r) := by
    have hh := iso_reachBall Γ c.symm huv
    rw [←hco] at hh
    change c.symm (ψ o)∈reachBall Γ o (2*r)
    simpa using hh
  change ψ∈(H : Set (Γ ≃g Γ))*displacement Γ o (2*r)
  exact Set.mem_mul.mpr ⟨c,hc,c⁻¹*ψ,hrem,by simp⟩

lemma displacement_approximate_of_doubling (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    IsApproximateSubgroup (K : ℝ) (displacement Γ o (2*r)) where
  one_mem := one_mem_displacement Γ o _
  inv_eq_self := by
    ext φ
    change φ⁻¹∈displacement Γ o (2*r) ↔ φ∈displacement Γ o (2*r)
    exact displacement_inv Γ
  sq_covBySMul := by
    apply (displacement_cover_of_doubling Γ hl ht o r K hd).subset_left
    rw [pow_two]
    simpa only [show 2*r+2*r=4*r by omega] using displacement_mul_subset Γ o (2*r) (2*r)

theorem compact_open_approximate_scales
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∀ R : ℕ, ∃ n≥R, IsCompact (displacement Γ o (2*n)) ∧
      IsOpen (displacement Γ o (2*n)) ∧
      IsApproximateSubgroup (5^(d+1) : ℝ) (displacement Γ o (2*n)) := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  dsimp only
  intro R
  obtain ⟨n,hn,hd⟩ := sparse_polynomial_doubling_scales
    (fun n => (reachBall Γ o n).ncard)
    (fun r s hrs => Set.ncard_le_ncard (reachBall_mono Γ o hrs) (reachBall_finite Γ hl o s))
    (fun n => (Set.ncard_pos (reachBall_finite Γ hl o n)).mpr ⟨o,reachBall_self Γ o n⟩)
    d hpoly R
  refine ⟨n,hn,compact_displacement Γ hc hl o _,open_displacement Γ o _,?_⟩
  exact_mod_cast displacement_approximate_of_doubling Γ hl ht o n (5^(d+1)) hd

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphGeneratingNeighborhood
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma displacement_eq_pow (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v)
    (o : X) (n : ℕ) : displacement Γ o (n+1)=displacement Γ o 1^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨p,hp⟩ := hg
      rw [pow_succ']
      generalize hx : g o=x at p
      cases p with
      | nil =>
        have hg1 : g∈displacement Γ o 1 := by
          change g o∈reachBall Γ o 1
          rw [hx]
          exact reachBall_self Γ o 1
        refine Set.mem_mul.mpr ⟨g,hg1,1,?_,mul_one g⟩
        rw [←ih]
        exact one_mem_displacement Γ o _
      | @cons a b c hab p =>
        obtain ⟨f,hf⟩ := ht o b
        have hfmem : f∈displacement Γ o 1 := by
          change f o∈reachBall Γ o 1
          rw [hf]
          exact ⟨SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil,by simp⟩
        have hrem : f⁻¹*g∈displacement Γ o (n+1) := by
          have hwalk : g o∈reachBall Γ b (n+1) := by
            rw [hx]
            exact ⟨p,by simpa using hp⟩
          have hh := iso_reachBall Γ f.symm hwalk
          rw [←hf] at hh
          change f.symm (g o)∈reachBall Γ o (n+1)
          simpa using hh
        refine Set.mem_mul.mpr ⟨f,hfmem,f⁻¹*g,?_,by simp⟩
        rw [←ih]
        exact hrem
    · rw [pow_succ',←ih]
      simpa only [show 1+(n+1)=n+1+1 by omega] using
        displacement_mul_subset Γ o 1 (n+1)

lemma displacement_powers_cover (hc : Γ.Connected)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (g : Γ ≃g Γ) :
    ∃ n : ℕ, g∈displacement Γ o 1^(n+1) := by
  obtain ⟨p⟩ := hc o (g o)
  refine ⟨p.length,?_⟩
  rw [←displacement_eq_pow Γ ht]
  exact ⟨p,Nat.le_succ _⟩

lemma displacement_generates (hc : Γ.Connected)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) :
    Subgroup.closure (displacement Γ o 1)=⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n,hn⟩ := displacement_powers_cover Γ hc ht o g
  have hpow : ∀ k : ℕ, displacement Γ o 1^k ⊆
      (Subgroup.closure (displacement Γ o 1) : Set (Γ ≃g Γ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      rintro a ⟨b,hb,c,hc,rfl⟩
      exact (Subgroup.closure _).mul_mem (ih hb) (Subgroup.subset_closure hc)
  exact hpow (n+1) hn

theorem compact_open_generating_approximate_powers
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    let S := displacement Γ o 1
    IsCompact S ∧ IsOpen S ∧ (1 : Γ ≃g Γ)∈S ∧ S⁻¹=S ∧
      Subgroup.closure S=⊤ ∧
      ∀ R : ℕ, ∃ n≥R, IsCompact (S^n) ∧ IsOpen (S^n) ∧
        IsApproximateSubgroup (5^(d+1) : ℝ) (S^n) := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  dsimp only
  refine ⟨compact_displacement Γ hc hl o 1,open_displacement Γ o 1,
    one_mem_displacement Γ o 1,?_,displacement_generates Γ hc ht o,?_⟩
  · ext g
    change g⁻¹∈displacement Γ o 1 ↔ g∈displacement Γ o 1
    exact displacement_inv Γ
  · intro R
    obtain ⟨n,hn,hcomp,hopen,happrox⟩ :=
      compact_open_approximate_scales Γ hc hl ht o d hpoly (max R 1)
    have he : displacement Γ o (2*n)=displacement Γ o 1^(2*n) := by
      have hpos : 0<2*n := by omega
      simpa only [Nat.sub_add_cancel (show 1≤2*n by omega)] using
        displacement_eq_pow Γ ht o (2*n-1)
    refine ⟨2*n,by omega,?_,?_,?_⟩ <;> rwa [←he]

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_TopologicalClassificationBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal Pointwise

namespace CriticalPercolation
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma uniform_compact_approximate_powers_of_sparse_polynomial
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    HasUniformCompactApproximatePowers Γ (5^(d+1)) := by
  let _ : TopologicalSpace X := ⊥
  let _ : DiscreteTopology X := ⟨rfl⟩
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  exact ⟨displacement Γ o 1,
    compact_open_generating_approximate_powers Γ hc hl ht o d hpoly⟩

end GraphTopology
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_topological_classification_counterexample_bs_oai [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) (o : V) :
    ∃ d : ℕ, 2≤d ∧ ∃ C : ℕ,
      (G.orbitPower o (2*C+1)).Connected ∧
      (MulAction.orbit G.Aut o).Infinite ∧
      (∀ u, ((G.orbitPower o (2*C+1)).neighborSet u).Finite) ∧
      (∀ u v, ∃ g : G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1), g u=v) ∧
      (∀ R : ℕ, ∃ n≥R, ∀ u : MulAction.orbit G.Aut o,
        (GraphTopology.reachBall (G.orbitPower o (2*C+1)) u n).ncard≤n^(d+1)) ∧
      GraphTopology.HasUniformCompactApproximatePowers
        (G.orbitPower o (2*C+1)) (5^(d+2)) ∧
      ¬GraphTopology.HasCompactOpenVirtuallyNilpotentQuotient
        (G.orbitPower o (2*C+1)) := by
  obtain ⟨hg,_,d,hd,hpoly⟩ := G.main_failure_sparse_polynomial hc hl hq hpc hper
  obtain ⟨C,Λ,hfg,hconn,hinf,hloc,htrans,hker,hreps,hscales⟩ :=
    G.sparse_polynomial_faithful_orbital_model hc hl hq o d hpoly
  let _ : Group.FG Λ := hfg
  have ht : ∀ u v, ∃ g : G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1), g u=v := by
    intro u v
    obtain ⟨g,hg⟩ := htrans u v
    exact ⟨g.val,hg⟩
  have hpow : GraphTopology.HasUniformCompactApproximatePowers
      (G.orbitPower o (2*C+1)) (5^(d+2)) := by
    apply GraphTopology.uniform_compact_approximate_powers_of_sparse_polynomial
      _ hconn hloc ht (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o) (d+1)
    intro R
    obtain ⟨n,hn,hh⟩ := hscales R
    exact ⟨n,hn,hh _⟩
  refine ⟨d,hd,C,hconn,hinf,hloc,ht,hscales,hpow,?_⟩
  rintro ⟨H,hn,hcomp,hopen,N,hnil,hN⟩
  let _ := hn
  let _ := hnil
  obtain ⟨S,hS,hcover⟩ := hreps
  exact hper (G.critical_null_of_compact_open_orbital_quotient_bs hc hl hg o (2*C+1)
    hconn Λ S hS hcover H N hN ⟨hcomp,hopen⟩ hpc)

end BondGraph
end CriticalPercolation
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs_oai.{u_1, u_2}
