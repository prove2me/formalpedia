-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:50:17.39226+00:00
-- url     : https://prove2.me/submissions/f7a167fa-1929-43dd-81bb-d7da98b20bf2

import Mathlib
import Definitions.Def_OAIQ078B002

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

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

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

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterObject
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

lemma incidentEdges_mono {S T : Set V} (h : S ⊆ T) : G.incidentEdges S ⊆ G.incidentEdges T := by
  rintro e ⟨v, hv, he⟩
  exact ⟨v, h hv, he⟩

end CriticalPercolation.BondGraph

end
end

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FourthMomentFatou
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace CriticalPercolation
variable {X : Type*} [MeasurableSpace X]

lemma lintegral_fourth_bound_of_tendsto (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (g : X → ℝ≥0∞) (C : ℝ≥0∞) (hm : ∀ n, Measurable (f n))
    (ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hb : ∀ n, (∫⁻ x, f n x ∂μ)^4≤C) : (∫⁻ x, g x ∂μ)^4≤C := by
  have hroot (n : ℕ) : (∫⁻ x, f n x ∂μ) ≤ C^((4:ℝ)⁻¹) := by
    apply (ENNReal.le_rpow_inv_iff (by norm_num : (0:ℝ)<4)).mpr
    simpa only [ENNReal.rpow_ofNat] using hb n
  have hlim : (∫⁻ x, g x ∂μ) ≤ C^((4:ℝ)⁻¹) := by
    calc _ = ∫⁻ x, liminf (fun n => f n x) atTop ∂μ := by
               apply lintegral_congr
               intro x
               exact (ht x).liminf_eq.symm
         _ ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := lintegral_liminf_le hm
         _ ≤ C^((4:ℝ)⁻¹) :=
           liminf_le_of_frequently_le (Eventually.frequently (Eventually.of_forall hroot))
  have h := (ENNReal.le_rpow_inv_iff (by norm_num : (0:ℝ)<4)).mp hlim
  simpa only [ENNReal.rpow_ofNat] using h

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_GeometricFourth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped ENNReal

namespace CriticalPercolation

lemma geometric_fourth_bound (I : ℝ≥0∞) (A : ℝ) (hA : 0≤A) (n : ℕ)
    (h : I^4≤ENNReal.ofReal (A/(16:ℝ)^n)) :
    I≤ENNReal.ofReal ((A+1)*(1/2:ℝ)^n) := by
  apply (ENNReal.pow_le_pow_left_iff (by decide : 4≠0)).mp
  rw [←ENNReal.ofReal_pow (by positivity)]
  apply h.trans (ENNReal.ofReal_le_ofReal _)
  have hpow : ((1/2:ℝ)^n)^4 = (1/16:ℝ)^n := by
    rw [←pow_mul,Nat.mul_comm n 4,pow_mul]
    norm_num
  rw [mul_pow,hpow,one_div_pow,mul_one_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsq : A≤(A+1)^2 := by nlinarith
  have ht : 1≤(A+1)^2 := by nlinarith
  nlinarith [sq_nonneg ((A+1)^2-1)]

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceSearch
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

namespace CriticalPercolation.IncidenceSearch

variable {V E : Type*} [DecidableEq E]

lemma compile_valid (G : BondGraph V E) (v : V) (n : ℕ) (st : State E) :
    (compile G v n st).Valid st.read := by
  induction n generalizing st with
  | zero => trivial
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · exact ⟨h.choose_spec.1,ih _,ih _⟩
    · trivial

lemma good_closed (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∉ ω) :
    Good G v ω (st.closed e) := by
  refine ⟨fun a ha => Finset.mem_insert_of_mem (hs.1 ha),?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_false (fun h => he.1 (hs.1 h)) hω
    · exact hs.2.1 a ha
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha

lemma good_open (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∈ ω) :
    Good G v ω (st.open e) := by
  refine ⟨Finset.insert_subset_insert e hs.1,?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_true (Finset.mem_insert_self _ _) hω
    · have hae : a≠e := fun hh => he.1 (hh ▸ ha)
      simpa only [State.open,Finset.mem_insert,hae,false_or] using hs.2.1 a ha
  · intro a ha
    change a ∈ G.incidentEdges (G.cluster ((insert e st.opened : Finset E) : Set E) v)
    rw [Finset.coe_insert]
    apply G.incidentEdges_mono (G.cluster_mono (Set.subset_insert e (st.opened : Set E)) v)
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha

lemma terminal_cluster (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (ht : ¬∃ e, Available G v st e) :
    G.cluster ω v = G.cluster (st.opened : Set E) v ∧
      (st.read : Set E) = G.incidentEdges (G.cluster ω v) := by
  have hread : ∀ e ∈ G.incidentEdges (G.cluster (st.opened : Set E) v), e ∈ st.read := by
    intro e he
    by_contra hh
    exact ht ⟨e,hh,he⟩
  have hc : G.cluster ω v = G.cluster (st.opened : Set E) v := by
    have hh := G.roots_eq_of_incident (S := {v}) (U := G.cluster (st.opened : Set E) v)
      (ω := (st.opened : Set E)) (ω' := ω)
      (by simp only [ClusterDeletion.roots_singleton,ClusterDeletion.component,BondGraph.cluster])
      (fun e he => hs.2.1 e (hread e he))
    simpa only [ClusterDeletion.roots_singleton,ClusterDeletion.component,BondGraph.cluster] using hh
  refine ⟨hc,?_⟩
  rw [hc]
  exact Set.Subset.antisymm hs.2.2 hread

variable [Fintype E]

lemma compile_terminal (G : BondGraph V E) (v : V) (ω : Set E) (n : ℕ) (st : State E)
    (hs : Good G v ω st) (hn : Fintype.card E - st.read.card < n) :
    let out := (compile G v n st).run (fun e => decide (e∈ω))
    Good G v ω out ∧ ¬∃ e, Available G v out e := by
  induction n generalizing st with
  | zero => omega
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : Available G v st e := h.choose_spec
      have hc : (insert e st.read).card = st.read.card+1 := Finset.card_insert_of_notMem he.1
      have hle : st.read.card < Fintype.card E := by
        have hh := Finset.card_le_univ (s := insert e st.read)
        rw [hc] at hh
        omega
      have hn' : Fintype.card E - (insert e st.read).card < n := by rw [hc]; omega
      simp only [SearchTree.run]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        Good G v ω out ∧ ¬∃ a, Available G v out a)
      by_cases hω : e∈ω
      · simp only [hω,decide_true,if_true]
        exact ih (st.open e) (good_open G v ω st hs e he hω) hn'
      · simp only [hω,decide_false,Bool.false_eq_true,if_false]
        exact ih (st.closed e) (good_closed G v ω st hs e he hω) hn'
    · exact ⟨hs,h⟩

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteProductPin
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

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype E] [Fintype A] in
lemma pin_nonneg (w : E → A → ℝ) (hw : ∀ e a, 0 ≤ w e a) (e : E) (b : A) :
    ∀ j a, 0 ≤ pin w e b j a := by
  intro j a
  by_cases h : j = e
  · subst j; simp [pin]; split_ifs <;> norm_num
  · simpa [pin,h] using hw j a

omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j

omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]

lemma expect_mask_pin (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [ite_eq_left h,ite_eq_left h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Potential
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

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_prop_mask_pin (w : E → Prop → ℝ) (e : E) (b : Prop) (f : (E → Prop) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  convert expect_mask_pin w e b f using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  by_cases h : ω e = b <;> simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Score
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

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma expect_prop_ite (w : E → Prop → ℝ) (e : E) (f g : Set E → ℝ) :
    expect w (fun ω => if ω e then f ω else g ω) =
      w e True*expect (pin w e True) f+w e False*expect (pin w e False) g := by
  calc
    _ = expect w (fun ω => (if ω e = True then f ω else 0) +
        (if ω e = False then g ω else 0)) := by
      congr 1
      funext ω
      by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert expect_prop_mask_pin w e True f using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert expect_prop_mask_pin w e False g using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]

end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dite_eq_right hje]
  exact hf j hj'.2

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceIdentity
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

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

variable [Fintype E]

lemma tree_valid (G : BondGraph V E) (v : V) : (tree G v).Valid ∅ :=
  compile_valid G v _ _

lemma tree_read (G : BondGraph V E) (v : V) (ω : Set E) :
    (((tree G v).run (fun e => decide (e∈ω))).read : Set E) =
      G.incidentEdges (G.cluster ω v) := by
  have hg : Good G v ω (⟨∅,∅⟩ : State E) := by simp [Good]
  have hh := compile_terminal G v ω (Fintype.card E+1) ⟨∅,∅⟩ hg (by simp)
  exact (terminal_cluster G v ω _ hh.1 hh.2).2

lemma tree_mem_read (G : BondGraph V E) (v : V) (ω : Set E) (e : E) :
    e ∈ ((tree G v).run (fun a => decide (a∈ω))).read ↔
      e ∈ G.incidentEdges (G.cluster ω v) := by
  exact Set.ext_iff.mp (tree_read G v ω) e

end CriticalPercolation.IncidenceSearch
end
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma restrictEdges_openGraph (s : Set E) (ω : Set E) :
    (G.restrictEdges s).openGraph (Subtype.val ⁻¹' ω) = G.openGraph (s ∩ ω) := by
  unfold openGraph restrictEdges
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists]
  constructor
  · rintro ⟨e, hs, hω, rfl⟩
    exact ⟨e, ⟨hs, hω⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hω⟩, rfl⟩
    exact ⟨e, hs, hω, rfl⟩

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterMassRestriction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma restrict_cluster (K : Set E) (ω : Set E) (v : V) :
    (G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) v = G.cluster (K ∩ ω) v := by
  simp only [BondGraph.cluster,G.restrictEdges_openGraph]

end CriticalPercolation.FiniteClusters
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

lemma measurableSet_heavyClusterEvent [Countable V] [Countable E] (o v : V) :
    MeasurableSet (G.heavyClusterEvent o v) :=
  measurableSet_eq_fun (G.measurable_modularClusterMass o v) measurable_const

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

lemma clusterPeaks_eq_of_reachable {ω : Set E} {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.clusterPeaks ω x = G.clusterPeaks ω y := by
  ext z
  exact and_congr (⟨fun hz => h.symm.trans hz,fun hz => h.trans hz⟩) Iff.rfl

lemma peakBound_iff_of_reachable (N : ℕ) {ω : Set E} {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.peakBound N ω x ↔ G.peakBound N ω y := by
  unfold peakBound
  rw [G.clusterPeaks_eq_of_reachable h]

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

lemma Aut.clusterPeaks_image (φ : G.Aut) (ω : Set E) (v : V) :
    φ.vertex '' G.clusterPeaks ω v = G.clusterPeaks (φ.edge '' ω) (φ.vertex v) := by
  ext z
  obtain ⟨y,rfl⟩ := φ.vertex.surjective z
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,clusterPeaks,Set.mem_ofPred_eq,
    φ.clusterPeak_iff]
  exact and_congr (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).symm Iff.rfl

lemma Aut.peakBound_iff (φ : G.Aut) (N : ℕ) (ω : Set E) (v : V) :
    G.peakBound N (φ.edge '' ω) (φ.vertex v) ↔ G.peakBound N ω v := by
  change (∃ S : Finset V, S.card ≤ N ∧ G.clusterPeaks (φ.edge '' ω) (φ.vertex v) ⊆ S) ↔ _
  rw [←φ.clusterPeaks_image]
  constructor
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex.symm,(Finset.card_image_le).trans hS,?_⟩
    intro x hx
    exact Finset.mem_image.mpr ⟨φ.vertex x,h ⟨x,hx,rfl⟩,φ.vertex.symm_apply_apply x⟩
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex,(Finset.card_image_le).trans hS,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact Finset.mem_image.mpr ⟨x,h hx,rfl⟩

lemma measurable_clusterPeak [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeak ω x) := by
  exact .forall (fun z => (G.measurable_reachable x z).imp measurable_const)

lemma measurable_mem_clusterPeaks [Countable V] [Countable E] (v x : V) :
    Measurable (fun ω : Set E => x∈G.clusterPeaks ω v) :=
  (G.measurable_reachable v x).and (G.measurable_clusterPeak x)

lemma measurable_peakBound [Countable V] [Countable E] (N : ℕ) (v : V) :
    Measurable (fun ω : Set E => G.peakBound N ω v) := by
  exact .exists (fun S : Finset V => measurable_const.and
    (.forall (fun x => (G.measurable_mem_clusterPeaks v x).imp measurable_const)))

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedMassTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma suborbitCard_mul_modularRatio (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (x y : V) :
    (G.suborbitCard y x : ℝ) * G.modularRatio x y = G.suborbitCard x y := by
  unfold modularRatio
  have hn : (G.suborbitCard y x : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x))
  field_simp

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedTransportENNReal
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
namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma enn_fiber_sum_root (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x : {x // x∈R.roots}) (y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  let := (G.stabilizerOrbit_finite hc hl x y).fintype
  rw [← (fiberEquiv G R x y).symm.tsum_eq]
  have hv (z : G.stabilizerOrbit x y) :
      ennRow G R F ((fiberEquiv G R x y).symm z) = F x y := by
    change F x z = F x y
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp z.property
    have hh := hF φ x y
    rwa [hx,hy] at hh
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (G.stabilizerOrbit x y) = G.suborbitCard x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]

lemma enn_fiber_sum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) (x y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ.vertex.symm y
  have hy : φ.vertex v = y := φ.vertex.apply_symm_apply y
  have hq : G.pairOrbit (φ.vertex u) y = G.pairOrbit u v := by
    rw [←hy,Aut.pairOrbit]
  rw [hq,enn_fiber_sum_root G R hc hl F hF ⟨u,hu⟩ v]
  change (G.suborbitCard u v : ℝ≥0∞) * F u v = _
  rw [←hy,Aut.suborbitCard,hF]

lemma tsum_ennRow (F : V → V → ℝ≥0∞) :
    (∑' p, ennRow G R F p) = ∑ x ∈ R.roots, ∑' y, F x y := by
  change (∑' p : {x // x∈R.roots} × V, F p.1 p.2) = _
  rw [ENNReal.tsum_prod (f := fun (x : {x // x∈R.roots}) y => F x y)]
  simp only [tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => ∑' y, F x y)

lemma tilted_massTransport_ennreal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) :
    (∑ x ∈ R.roots, ∑' y, F x y) =
      ∑ y ∈ R.roots, ∑' x, F x y * G.stabilizerWeight y x := by
  let F' := fun x y => F y x * G.stabilizerWeight x y
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := by
    simp only [F',hF,Aut.stabilizerWeight]
  have heq : (∑' p, ennRow G R F p) = (∑' p, ennRow G R F' p) := by
    calc
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q}, ennRow G R F p :=
        (ENNReal.tsum_fiberwise _ _).symm
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          ennRow G R F' p := by
        apply tsum_congr
        intro q
        induction q using Quotient.inductionOn' with
        | h p =>
          change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2}, ennRow G R F z) =
            ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1}, ennRow G R F' z
          rw [enn_fiber_sum G R hc hl F hF,enn_fiber_sum G R hc hl F' hF']
          have hbal : (G.suborbitCard p.2 p.1 : ℝ≥0∞) * G.stabilizerWeight p.2 p.1 =
              (G.suborbitCard p.1 p.2 : ℝ≥0∞) := by
            unfold stabilizerWeight
            rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _),
              G.suborbitCard_mul_modularRatio hc hl,ENNReal.ofReal_natCast]
          simp only [F']
          rw [mul_left_comm, hbal, mul_comm]
      _ = ∑' p, ennRow G R F' p :=
        (G.swapPairOrbit.tsum_eq _).trans (ENNReal.tsum_fiberwise _ _)
  rw [tsum_ennRow G R F,tsum_ennRow G R F'] at heq
  exact heq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RandomTiltedTransport
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
variable {V E : Type*} [Countable V] (G : BondGraph V E)

omit [Countable V] in
lemma expected_enn_transport_aut (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (φ : G.Aut) (x y : V) :
    (∫⁻ ω, F ω (φ.vertex x) (φ.vertex y) ∂G.law p) = ∫⁻ ω, F ω x y ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [lintegral_map (hm _ _) (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [ha]

lemma OrbitRepresentatives.random_tilted_transport (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y) :
    (∑ x ∈ R.roots, ∫⁻ ω, ∑' y, F ω x y ∂G.law p) =
      ∑ y ∈ R.roots, ∫⁻ ω, ∑' x, F ω x y * G.stabilizerWeight y x ∂G.law p := by
  simp_rw [lintegral_tsum (fun y => (hm _ y).aemeasurable),
    lintegral_tsum (fun x => ((hm x _).mul_const _).aemeasurable),
    lintegral_mul_const _ (hm _ _)]
  exact OrbitRepresentatives.tilted_massTransport_ennreal G R hc hl _ (G.expected_enn_transport_aut p F hm ha)

lemma OrbitRepresentatives.incoming_finite_ae (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (N : ℝ≥0∞) (hN : N < ∞) (hb : ∀ ω x, ∑' y, F ω x y ≤ N) (v : V) :
    ∀ᵐ ω ∂G.law p, (∑' x, F ω x v * G.stabilizerWeight v x) < ∞ := by
  have hout : (∑ x ∈ R.roots, ∫⁻ ω, ∑' y, F ω x y ∂G.law p) < ∞ := by
    apply ENNReal.sum_lt_top.mpr
    intro x hx
    exact (calc
      (∫⁻ ω, ∑' y, F ω x y ∂G.law p) ≤ ∫⁻ _ : Set E, N ∂G.law p :=
        lintegral_mono (fun ω => hb ω x)
      _ = N := by simp).trans_lt hN
  rw [OrbitRepresentatives.random_tilted_transport G R hc hl p F hm ha] at hout
  obtain ⟨u,hu,φ,rfl⟩ := R.cover v
  have hu' : (∫⁻ ω, ∑' x, F ω x u * G.stabilizerWeight u x ∂G.law p) < ∞ :=
    (Finset.single_le_sum (fun _ _ => zero_le) hu).trans_lt hout
  have he : (∫⁻ ω, ∑' x, F ω x (φ.vertex u) * G.stabilizerWeight (φ.vertex u) x ∂G.law p) =
      ∫⁻ ω, ∑' x, F ω x u * G.stabilizerWeight u x ∂G.law p := by
    conv_lhs => rw [←G.law_map_aut p φ]
    rw [lintegral_map (Measurable.tsum (fun x => (hm x _).mul_const _))
      (BernoulliProduct.measurable_image_equiv φ.edge)]
    apply lintegral_congr
    intro ω
    rw [←φ.vertex.tsum_eq]
    simp only [ha,Aut.stabilizerWeight]
  exact ae_lt_top (Measurable.tsum (fun x => (hm x _).mul_const _)) (he.trans_lt hu').ne

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyPeaks
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_heavyPeakTransport (N : ℕ) (x y : V) :
    Measurable (fun ω : Set E => G.heavyPeakTransport N ω x y) := by
  apply measurable_const.ite _ measurable_const
  exact (G.measurableSet_heavyClusterEvent x x).inter
    ((G.measurable_peakBound N x).and (G.measurable_mem_clusterPeaks x y)).setOf

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_aut (N : ℕ) (φ : G.Aut) (ω : Set E) (x y : V) :
    G.heavyPeakTransport N (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.heavyPeakTransport N ω x y := by
  unfold heavyPeakTransport
  rw [←φ.cluster_image,φ.modularMass_image,φ.peakBound_iff,←φ.clusterPeaks_image]
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_out_bound (N : ℕ) (ω : Set E) (x : V) :
    (∑' y, G.heavyPeakTransport N ω x y) ≤ N := by
  by_cases hb : G.peakBound N ω x
  · obtain ⟨S,hS,hcover⟩ := hb
    calc
      _ ≤ ∑' y, if y∈S then (1 : ℝ≥0∞) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro y
        unfold heavyPeakTransport
        split_ifs with hh hs
        · rfl
        · exact False.elim (hs (hcover hh.2.2))
        · exact zero_le
        · rfl
      _ = (S.card : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun y hy => ite_eq_right hy)]
        calc
          _ = ∑ y ∈ S, (1 : ℝ≥0∞) := Finset.sum_congr rfl (fun y hy => ite_eq_left hy)
          _ = _ := by simp
      _ ≤ N := by exact_mod_cast hS
  · simp only [heavyPeakTransport,hb,false_and,and_false,if_false,tsum_zero,zero_le]

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_infinite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (N : ℕ) (ω : Set E) (y : V)
    (hh : G.modularMass y (G.cluster ω y) = ∞) (hb : G.peakBound N ω y)
    (hp : G.clusterPeak ω y) :
    (∑' x, G.heavyPeakTransport N ω x y * G.stabilizerWeight y x) = ∞ := by
  apply top_unique
  rw [←hh]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ G.cluster ω y
  · have hxy : (G.openGraph ω).Reachable x y := hx.symm
    have he : G.cluster ω x = G.cluster ω y := G.cluster_eq_of_reachable hxy
    have hhx : G.modularMass x (G.cluster ω x) = ∞ := by
      rw [he,G.modularMass_eq_top_change_base hc hl x y]
      exact hh
    have hbx : G.peakBound N ω x := (G.peakBound_iff_of_reachable N hxy).mpr hb
    have hcond : G.modularMass x (G.cluster ω x) = ∞ ∧ G.peakBound N ω x ∧
        y∈G.clusterPeaks ω x := ⟨hhx,hbx,⟨hxy,hp⟩⟩
    simp only [ite_eq_left hx,heavyPeakTransport,ite_eq_left hcond,one_mul,le_refl]
  · simp only [ite_eq_right hx,zero_le]

lemma no_heavy_finite_peaks_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (p : unitInterval) :
    ∀ᵐ ω ∂G.law p, ∀ y : V, ∀ N : ℕ,
      ¬ (G.modularMass y (G.cluster ω y) = ∞ ∧ G.peakBound N ω y ∧ G.clusterPeak ω y) := by
  apply ae_all_iff.mpr
  intro y
  apply ae_all_iff.mpr
  intro N
  have hfin := OrbitRepresentatives.incoming_finite_ae G (G.orbitRepresentatives hq)
    hc hl p (G.heavyPeakTransport N) (G.measurable_heavyPeakTransport N)
    (G.heavyPeakTransport_aut N) N (ENNReal.natCast_lt_top N) (G.heavyPeakTransport_out_bound N) y
  filter_upwards [hfin] with ω hω
  rintro ⟨hh,hb,hp⟩
  rw [G.heavyPeakTransport_infinite hc hl N ω y hh hb hp] at hω
  exact (lt_irrefl _ hω)

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakRatioTransport
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

lemma one_le_modularClusterMass (ω : Set E) (x : V) :
    1 ≤ G.modularMass x (G.cluster ω x) := by
  have h := ENNReal.le_tsum (f := fun y => if y∈G.cluster ω x then G.stabilizerWeight x y else 0) x
  have hx : x∈G.cluster ω x := SimpleGraph.Reachable.refl x
  simpa only [modularMass,ite_eq_left hx,G.stabilizerWeight_self] using h

lemma stabilizerWeight_eq_one_of_peaks (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (hr : (G.openGraph ω).Reachable x y)
    (hx : G.clusterPeak ω x) (hy : G.clusterPeak ω y) :
    G.stabilizerWeight x y = 1 := by
  apply le_antisymm (hx y hr)
  have h := (G.stabilizerWeight_le_one_iff hc hl x y x).mp (hy x hr.symm)
  simpa only [G.stabilizerWeight_self] using h

lemma measurable_peakRatioTransport [Countable V] [Countable E] (x y : V) :
    Measurable (fun ω : Set E => G.peakRatioTransport ω x y) := by
  apply Measurable.ite (G.measurable_mem_clusterPeaks x y).setOf _ measurable_const
  apply Measurable.mul (G.measurable_modularClusterMass y x).inv
  apply Measurable.inv
  apply Measurable.of_discrete.comp
  apply measurable_ncard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

lemma peakRatioTransport_aut (φ : G.Aut) (ω : Set E) (x y : V) :
    G.peakRatioTransport (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.peakRatioTransport ω x y := by
  unfold peakRatioTransport
  rw [←φ.cluster_image,φ.modularMass_image,←φ.clusterPeaks_image,
    Set.ncard_image_of_injective _ φ.vertex.injective]
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

lemma clusterPeakRatio_eq_zero_of_heavy (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hh : G.modularMass x (G.cluster ω x) = ∞) :
    G.clusterPeakRatio ω x = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro y
  unfold peakRatioTransport
  split_ifs
  · have hy : G.modularMass y (G.cluster ω x) = ∞ :=
      (G.modularMass_eq_top_change_base hc hl x y _).mp hh
    simp [hy]
  · rfl

lemma clusterPeakRatio_eq_inv_mass (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x y : V) (hh : G.modularMass x (G.cluster ω x) ≠ ∞)
    (hy : y∈G.clusterPeaks ω x) :
    G.clusterPeakRatio ω x = (G.modularMass y (G.cluster ω x))⁻¹ := by
  have hf := G.clusterPeaks_finite_of_mass_ne_top hc hl ω x hh
  have hnon := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω x hh
  have hpos : (G.clusterPeaks ω x).ncard ≠ 0 := (Set.ncard_pos hf).mpr hnon |>.ne'
  unfold clusterPeakRatio
  rw [tsum_eq_sum (s := hf.toFinset) (fun z hz => by
    simp only [hf.mem_toFinset] at hz
    simp only [peakRatioTransport,ite_eq_right hz])]
  have heq (z : V) (hz : z ∈ hf.toFinset) : G.peakRatioTransport ω x z =
      (G.modularMass y (G.cluster ω x))⁻¹ * ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹ := by
    have hz' := hf.mem_toFinset.mp hz
    rw [peakRatioTransport,ite_eq_left hz',G.modularMass_change_base hc hl z y,
      G.stabilizerWeight_eq_one_of_peaks hc hl ω (hz'.1.symm.trans hy.1) hz'.2 hy.2,one_mul]
  rw [Finset.sum_congr rfl heq]
  simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
  rw [←mul_assoc,mul_comm ((G.clusterPeaks ω x).ncard : ℝ≥0∞),mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast hpos) (ENNReal.natCast_ne_top _),mul_one]

lemma clusterPeakRatio_le_one (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) : G.clusterPeakRatio ω x ≤ 1 := by
  by_cases hh : G.modularMass x (G.cluster ω x) = ∞
  · rw [G.clusterPeakRatio_eq_zero_of_heavy hc hl ω x hh]
    exact zero_le
  · obtain ⟨y,hy⟩ := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω x hh
    rw [G.clusterPeakRatio_eq_inv_mass hc hl ω x y hh hy,
      G.cluster_eq_of_reachable hy.1]
    exact (ENNReal.inv_le_one).mpr (G.one_le_modularClusterMass ω y)

lemma peakRatioTransport_incoming (ω : Set E) (y : V) :
    (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
      if G.clusterPeak ω y ∧ G.modularMass y (G.cluster ω y) ≠ ∞ then
        ((G.clusterPeaks ω y).ncard : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hp : G.clusterPeak ω y
  · have heq : (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
        ((G.modularMass y (G.cluster ω y))⁻¹ * ((G.clusterPeaks ω y).ncard : ℝ≥0∞)⁻¹) *
          G.modularMass y (G.cluster ω y) := by
      conv_rhs => rhs; unfold modularMass
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      by_cases hx : x∈G.cluster ω y
      · rw [ite_eq_left hx,peakRatioTransport,ite_eq_left ⟨hx.symm,hp⟩,
          G.cluster_eq_of_reachable hx.symm,G.clusterPeaks_eq_of_reachable hx.symm]
      · have hnot : y∉G.clusterPeaks ω x := fun h => hx h.1.symm
        simp only [peakRatioTransport,ite_eq_right hnot,zero_mul,ite_eq_right hx,mul_zero]
    rw [heq]
    by_cases hm : G.modularMass y (G.cluster ω y) = ∞
    · simp [hp,hm]
    · rw [ite_eq_left ⟨hp,hm⟩,mul_right_comm,
        ENNReal.inv_mul_cancel (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω y))) hm,
        one_mul]
  · have hz : ∀ x, G.peakRatioTransport ω x y = 0 := by
      intro x
      exact ite_eq_right (fun h => hp h.2)
    simp only [hz,zero_mul,tsum_zero,hp,false_and,if_false]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakReturn
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurable_peakReturn [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.peakReturn ω x) := by
  apply Measurable.ite (G.measurable_clusterPeak x).setOf _ measurable_const
  apply Measurable.inv
  apply (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
  apply measurable_encard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

lemma peakReturn_eq_inv_ncard (ω : Set E) (x : V) (hp : G.clusterPeak ω x)
    (hf : (G.clusterPeaks ω x).Finite) :
    G.peakReturn ω x = ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹ := by
  rw [peakReturn,ite_eq_left hp,hf.encard_eq_coe,ENat.toENNReal_coe]
  rfl

lemma peakReturn_le_one (ω : Set E) (x : V) : G.peakReturn ω x ≤ 1 := by
  unfold peakReturn
  split_ifs with hp
  · apply ENNReal.inv_le_one.mpr
    have hh : (1 : ℕ∞) ≤ (G.clusterPeaks ω x).encard :=
      Set.one_le_encard_iff_nonempty.mpr ⟨x,SimpleGraph.Reachable.refl x,hp⟩
    exact_mod_cast hh
  · exact zero_le

lemma peakRatioTransport_incoming_ae [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (y : V) :
    ∀ᵐ ω ∂G.law p, (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
      G.peakReturn ω y := by
  filter_upwards [G.no_heavy_finite_peaks_ae hc hl hq p] with ω hω
  rw [G.peakRatioTransport_incoming]
  by_cases hp : G.clusterPeak ω y
  · by_cases hm : G.modularMass y (G.cluster ω y) = ∞
    · have hi : (G.clusterPeaks ω y).Infinite := by
        intro hf
        exact hω y hf.toFinset.card ⟨hm,⟨hf.toFinset,le_rfl,fun _ hx => hf.mem_toFinset.mpr hx⟩,hp⟩
      simp [peakReturn,hp,hm,hi.encard_eq]
    · rw [ite_eq_left ⟨hp,hm⟩,G.peakReturn_eq_inv_ncard ω y hp
        (G.clusterPeaks_finite_of_mass_ne_top hc hl ω y hm)]
  · simp only [hp,false_and,if_false,peakReturn]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedPeakTransport
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

lemma clusterPeakRatio_eq_of_reachable (ω : Set E) {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.clusterPeakRatio ω x=G.clusterPeakRatio ω y := by
  unfold clusterPeakRatio peakRatioTransport
  simp only [G.cluster_eq_of_reachable h,G.clusterPeaks_eq_of_reachable h]

lemma measurable_clusterPeakRatio [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeakRatio ω x) :=
  Measurable.tsum (fun y => G.measurable_peakRatioTransport x y)

lemma Aut.clusterPeakRatio (φ : G.Aut) (ω : Set E) (x : V) :
    G.clusterPeakRatio (φ.edge '' ω) (φ.vertex x)=G.clusterPeakRatio ω x := by
  unfold CriticalPercolation.BondGraph.clusterPeakRatio
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro y
  exact G.peakRatioTransport_aut φ ω x y

lemma weighted_peakRatio_incoming (F : (Set E) → V → ℝ≥0∞)
    (hc : ∀ ω x y, (G.openGraph ω).Reachable x y → F ω x=F ω y)
    (ω : Set E) (y : V) :
    (∑' x, (F ω x*G.peakRatioTransport ω x y)*G.stabilizerWeight y x) =
      F ω y*(∑' x, G.peakRatioTransport ω x y*G.stabilizerWeight y x) := by
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  by_cases hx : y∈G.clusterPeaks ω x
  · rw [hc ω x y hx.1,mul_assoc]
  · simp only [peakRatioTransport,ite_eq_right hx,mul_zero,zero_mul]

theorem expected_weighted_peakRatio [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (F : (Set E) → V → ℝ≥0∞)
    (hm : ∀ x, Measurable (fun ω => F ω x))
    (ha : ∀ (φ : G.Aut) ω x, F (φ.edge '' ω) (φ.vertex x)=F ω x)
    (hr : ∀ ω x y, (G.openGraph ω).Reachable x y → F ω x=F ω y) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, F ω x*G.clusterPeakRatio ω x ∂G.law p) =
    ∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, F ω x*G.peakReturn ω x ∂G.law p := by
  have h := OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
    (fun ω x y => F ω x*G.peakRatioTransport ω x y)
    (fun x y => (hm x).mul (G.measurable_peakRatioTransport x y))
    (fun φ ω x y => by rw [ha φ ω x,G.peakRatioTransport_aut φ ω x y])
  simp only [ENNReal.tsum_mul_left,G.weighted_peakRatio_incoming F hr] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro x _
  apply lintegral_congr_ae
  filter_upwards [G.peakRatioTransport_incoming_ae hc hl hq p x] with ω hω
  rw [hω]

lemma measurable_normalizedClusterVolume [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.normalizedClusterVolume ω x) := by
  unfold normalizedClusterVolume
  exact measurable_const.ite
    (measurableSet_eq_fun (G.measurable_clusterPeakRatio x) measurable_const)
    (G.measurable_clusterPeakRatio x).inv

lemma Aut.normalizedClusterVolume (φ : G.Aut) (ω : Set E) (x : V) :
    G.normalizedClusterVolume (φ.edge '' ω) (φ.vertex x)=G.normalizedClusterVolume ω x := by
  unfold CriticalPercolation.BondGraph.normalizedClusterVolume
  rw [φ.clusterPeakRatio]

lemma normalizedClusterVolume_eq_of_reachable (ω : Set E) {x y : V}
    (h : (G.openGraph ω).Reachable x y) :
    G.normalizedClusterVolume ω x=G.normalizedClusterVolume ω y := by
  unfold normalizedClusterVolume
  rw [G.clusterPeakRatio_eq_of_reachable ω h]

lemma normalizedClusterVolume_eq_at_peak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x) (hf : G.modularMass x (G.cluster ω x)≠∞) :
    G.normalizedClusterVolume ω x=G.modularMass x (G.cluster ω x) := by
  rw [normalizedClusterVolume,G.clusterPeakRatio_eq_inv_mass hc hl ω x x hf
    ⟨SimpleGraph.Reachable.refl x,hp⟩,ite_eq_right (ENNReal.inv_ne_zero.mpr hf),inv_inv]

lemma normalizedClusterVolume_mul_ratio_le (ω : Set E) (x : V) :
    G.normalizedClusterVolume ω x*G.clusterPeakRatio ω x≤1 := by
  unfold normalizedClusterVolume
  split_ifs with h
  · simp
  · by_cases ht : G.clusterPeakRatio ω x=∞
    · simp [ht]
    · rw [ENNReal.inv_mul_cancel h ht]

theorem expected_peak_volume_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    (∑ x∈(G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.normalizedClusterVolume ω x*G.peakReturn ω x ∂G.law p) ≤
    (G.orbitRepresentatives hq).roots.card := by
  rw [←G.expected_weighted_peakRatio hc hl hq p G.normalizedClusterVolume
    G.measurable_normalizedClusterVolume (fun φ => φ.normalizedClusterVolume)
    (fun ω _ _ h => G.normalizedClusterVolume_eq_of_reachable ω h)]
  calc _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro x _
        calc _ ≤ ∫⁻ ω, (1 : ℝ≥0∞) ∂G.law p := lintegral_mono (fun ω =>
              G.normalizedClusterVolume_mul_ratio_le ω x)
             _ = 1 := by simp
       _ = _ := by simp

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakVolumeBand
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

lemma measurable_peakVolumeBand [Countable V] [Countable E] (T U : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.peakVolumeBand T U ω x) := by
  unfold peakVolumeBand
  exact (G.measurable_peakReturn x).ite
    ((measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)).inter
      (measurableSet_lt (G.measurable_normalizedClusterVolume x) measurable_const)) measurable_const

lemma peakVolumeBand_le_one (T U : ℝ≥0∞) (ω : Set E) (x : V) : G.peakVolumeBand T U ω x≤1 := by
  unfold peakVolumeBand
  split_ifs
  · exact G.peakReturn_le_one ω x
  · exact zero_le

lemma peakVolumeBand_support (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) (h : G.peakVolumeBand T U ω x≠0) :
    G.clusterPeak ω x ∧ T≤G.modularMass x (G.cluster ω x) ∧
      G.modularMass x (G.cluster ω x)<U := by
  have hb : T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U := by
    by_contra hn
    exact h (ite_eq_right hn)
  have hp : G.clusterPeak ω x := by
    by_contra hn
    exact h (by simp only [peakVolumeBand,ite_eq_left hb,peakReturn,ite_eq_right hn])
  have hm : G.modularMass x (G.cluster ω x)≠∞ := by
    intro he
    have hz := G.clusterPeakRatio_eq_zero_of_heavy hc hl ω x he
    have hvol : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,hz]
    rw [hvol] at hb
    exact (not_le.mpr hT) hb.1
  rw [G.normalizedClusterVolume_eq_at_peak hc hl ω x hp hm] at hb
  exact ⟨hp,hb⟩

lemma peakVolumeBand_mul_le (T U : ℝ≥0∞) (ω : Set E) (x : V) :
    T*G.peakVolumeBand T U ω x ≤ G.normalizedClusterVolume ω x*G.peakReturn ω x := by
  unfold peakVolumeBand
  split_ifs with h
  · gcongr
    exact h.1
  · simp

theorem expected_peakVolumeBand_mul_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (T U : ℝ≥0∞) :
    T*(∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, G.peakVolumeBand T U ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card := by
  calc _ = ∑ x∈(G.orbitRepresentatives hq).roots,
      ∫⁻ ω, T*G.peakVolumeBand T U ω x ∂G.law p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        exact (lintegral_const_mul'' T (G.measurable_peakVolumeBand T U x).aemeasurable).symm
       _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots,
          ∫⁻ ω, G.normalizedClusterVolume ω x*G.peakReturn ω x ∂G.law p := by
        apply Finset.sum_le_sum
        intro x _
        exact lintegral_mono (fun ω => G.peakVolumeBand_mul_le T U ω x)
       _ ≤ _ := G.expected_peak_volume_le hc hl hq p

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularIncidence
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

lemma bondWeight_ne_top (o : V) (e : E) : G.bondWeight o e ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro v hv
  exact G.stabilizerWeight_ne_top o v

lemma bondWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (e : E) : G.bondWeight o e = G.stabilizerWeight o a * G.bondWeight a e := by
  unfold bondWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact G.stabilizerWeight_change_base hc hl o a v

lemma Aut.bondWeight (φ : G.Aut) (o : V) (e : E) :
    G.bondWeight (φ.vertex o) (φ.edge e) = G.bondWeight o e := by
  unfold CriticalPercolation.BondGraph.bondWeight
  rw [φ.preserves]
  have himg : (Sym2.map φ.vertex (G.ends e)).toFinset = (G.ends e).toFinset.image φ.vertex := by
    ext v
    simp only [Sym2.mem_toFinset,Sym2.mem_map,Finset.mem_image]
  rw [himg,Finset.sum_image]
  · simp only [Aut.stabilizerWeight]
  · exact fun _ _ _ _ h => φ.vertex.injective h

lemma incidence_stabilizerOrbit_subset_ball (v w : V) (n : ℕ) (hw : w∈G.vertexBall v n) :
    G.stabilizerOrbit v w ⊆ G.vertexBall v n := by
  intro z hz
  obtain ⟨φ,hv,hwz⟩ := G.mem_stabilizerOrbit.mp hz
  have h := (Aut.vertexBall_mem G φ v w n).mpr hw
  simpa only [hv,hwz] using h

lemma stabilizerWeight_le_ball_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) {v w : V}
    (_hw : w∈G.vertexBall v 1) (hv : v∈G.vertexBall w 1) :
    G.stabilizerWeight v w ≤ K := by
  unfold stabilizerWeight modularRatio
  apply ENNReal.ofReal_le_of_le_toReal
  simp only [ENNReal.toReal_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl v w))).mpr
  have hnum : G.suborbitCard w v ≤ K :=
    (Set.ncard_le_ncard (G.incidence_stabilizerOrbit_subset_ball w v 1 hv)
      (G.vertexBall_finite hl w 1)).trans (hK w)
  have hden : (1:ℝ)≤G.suborbitCard v w := by exact_mod_cast G.suborbitCard_pos hc hl v w
  exact (Nat.cast_le.mpr hnum).trans (by nlinarith [show (0:ℝ)≤K by positivity])

lemma common_bond_ball_one {v w : V} {e : E} (hv : v∈G.ends e) (hw : w∈G.ends e) :
    w∈G.vertexBall v 1 := by
  by_cases he : v=w
  · subst w
    exact G.mem_vertexBall_self v 1
  · apply G.vertexBall_step (G.mem_vertexBall_self v 0)
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨?_,he⟩
    refine ⟨e,Set.mem_univ e,?_⟩
    exact (Sym2.mem_and_mem_iff he).mp ⟨hv,hw⟩

lemma bondWeight_le_at_end (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o v : V) (e : E)
    (hv : v∈G.ends e) : G.bondWeight o e ≤ (2*K : ℕ)*G.stabilizerWeight o v := by
  rw [G.bondWeight_change_base hc hl o v]
  have hsum : G.bondWeight v e ≤ (2*K : ℕ) := by
    calc
      _ ≤ ∑ w∈(G.ends e).toFinset, (K : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' : w∈G.ends e := Sym2.mem_toFinset.mp hw
        exact G.stabilizerWeight_le_ball_bound hc hl K hK
          (G.common_bond_ball_one hv hw') (G.common_bond_ball_one hw' hv)
      _ = ((G.ends e).toFinset.card * K : ℕ) := by simp [nsmul_eq_mul]
      _ ≤ (2*K : ℕ) := by
        have hh : (G.ends e).toFinset.card≤2 := by
          rw [Sym2.card_toFinset]
          split_ifs <;> omega
        exact_mod_cast Nat.mul_le_mul_right K hh
  calc _ ≤ G.stabilizerWeight o v * (2*K : ℕ) := by gcongr
       _ = _ := mul_comm _ _

lemma weighted_incidence_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o : V) (S : Set V) :
    (∑' e : E, if e∈G.incidentEdges S then G.bondWeight o e else 0) ≤
      (D*(2*K) : ℕ)*G.modularMass o S := by
  calc
    _ ≤ ∑' e : E, ∑' v : V, if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0 := by
      apply ENNReal.tsum_le_tsum
      intro e
      by_cases he : e∈G.incidentEdges S
      · rw [ite_eq_left he]
        obtain ⟨v,hv,hve⟩ := he
        simpa only [ite_eq_left (show v∈S ∧ v∈G.ends e from ⟨hv,hve⟩)] using
          (ENNReal.le_tsum v (f := fun v => if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0))
      · simp only [ite_eq_right he]; exact zero_le
    _ = ∑' v : V, ∑' e : E, if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0 :=
      ENNReal.tsum_comm
    _ ≤ ∑' v : V, if v∈S then (D*(2*K) : ℕ)*G.stabilizerWeight o v else 0 := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : v∈S
      · simp only [hv,true_and,if_true]
        have hf : (G.incidentEdges {v}).Finite := by simpa [incidentEdges] using hl v
        have hm (e : E) : e∈G.incidentEdges {v} ↔ v∈G.ends e := by
          simp [incidentEdges]
        have ht : (∑' e : E, if v∈G.ends e then G.bondWeight o e else 0) =
            ∑ e∈hf.toFinset, G.bondWeight o e := by
          rw [tsum_eq_sum (s := hf.toFinset) (fun e he => by
            simp only [hf.mem_toFinset,hm] at he
            exact ite_eq_right he)]
          apply Finset.sum_congr rfl
          intro e he
          exact ite_eq_left ((hm e).mp (hf.mem_toFinset.mp he))
        rw [ht]
        calc
          _ ≤ ∑ e∈hf.toFinset, (2*K : ℕ)*G.stabilizerWeight o v := by
            apply Finset.sum_le_sum
            intro e he
            exact G.bondWeight_le_at_end hc hl K hK o v e ((hm e).mp (hf.mem_toFinset.mp he))
          _ = ((G.incidentEdges {v}).ncard : ℝ≥0∞)*((2*K : ℕ)*G.stabilizerWeight o v) := by
            simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
          _ ≤ (D : ℝ≥0∞)*((2*K : ℕ)*G.stabilizerWeight o v) := by
            gcongr
            exact_mod_cast hD v
          _ = _ := by simp only [Nat.cast_mul,mul_assoc]
      · simp only [hv,false_and,if_false,tsum_zero,le_refl]
    _ = _ := by
      unfold modularMass
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      split_ifs <;> simp

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma abs_centeredCoefficient_le_one (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (e : E) :
    |centeredCoefficient p ω e|≤1 := by
  unfold centeredCoefficient
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [hp.1,hp.2]

lemma norm_weightedIncidenceTerm_le (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (x : V) (e : E) :
    ‖G.weightedIncidenceTerm p ω x e‖ ≤
      (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
  unfold weightedIncidenceTerm
  split_ifs
  · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_centeredCoefficient_le_one p hp ω e)
  · simp

lemma summable_weightedIncidence_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (ω : Set E) (x : V)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Summable (fun e => (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal) := by
  apply ENNReal.summable_toReal
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
    (G.weighted_incidence_le hc hl D K hD hK x _)

lemma abs_weightedDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1)
    (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    |G.weightedDiscrepancy p ω x| ≤ (D*(2*K) : ℕ)*(G.modularMass x (G.cluster ω x)).toReal := by
  have hs := G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm
  calc
    _ ≤ ∑' e, (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal :=
      tsum_of_norm_bounded hs.hasSum (G.norm_weightedIncidenceTerm_le p hp ω x)
    _ = (∑' e : E, if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro e
      split_ifs
      · exact G.bondWeight_ne_top x e
      · exact ENNReal.zero_ne_top
    _ ≤ ((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
        (G.weighted_incidence_le hc hl D K hD hK x _)
    _ = _ := by rw [ENNReal.toReal_mul,ENNReal.toReal_natCast]

lemma measurable_weightedDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.weightedDiscrepancy p ω x) := by
  apply Measurable.tsum
  intro e
  unfold weightedIncidenceTerm centeredCoefficient
  apply Measurable.ite
    (Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)).setOf
    _ measurable_const
  exact measurable_const.mul (measurable_const.ite (measurable_set_mem e).setOf measurable_const)

lemma weightedIncidenceTerm_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) (x y : V) (h : (G.openGraph ω).Reachable x y) (e : E) :
    G.weightedIncidenceTerm p ω x e =
      (G.stabilizerWeight x y).toReal*G.weightedIncidenceTerm p ω y e := by
  unfold weightedIncidenceTerm
  rw [G.cluster_eq_of_reachable h,G.bondWeight_change_base hc hl x y,ENNReal.toReal_mul]
  split_ifs <;> ring

lemma weightedDiscrepancy_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) (x y : V) (h : (G.openGraph ω).Reachable x y) :
    G.weightedDiscrepancy p ω x = (G.stabilizerWeight x y).toReal*G.weightedDiscrepancy p ω y := by
  unfold weightedDiscrepancy
  simp only [G.weightedIncidenceTerm_change_base hc hl p ω x y h,tsum_mul_left]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_NormalizedDiscrepancy
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

lemma measurable_normalizedAbsoluteDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.normalizedAbsoluteDiscrepancy p ω x) :=
  (G.measurable_weightedDiscrepancy p x).norm.ennreal_ofReal.div
    (G.measurable_modularClusterMass x x)

lemma Aut.weightedDiscrepancy (φ : G.Aut) (p : ℝ) (ω : Set E) (x : V) :
    G.weightedDiscrepancy p (φ.edge '' ω) (φ.vertex x) = G.weightedDiscrepancy p ω x := by
  unfold CriticalPercolation.BondGraph.weightedDiscrepancy
  rw [←φ.edge.tsum_eq]
  apply tsum_congr
  intro e
  unfold weightedIncidenceTerm centeredCoefficient
  rw [←φ.cluster_image]
  have hend (v : V) : φ.vertex v∈G.ends (φ.edge e) ↔ v∈G.ends e := by
    rw [φ.preserves]
    simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]
  have hi : φ.edge e∈G.incidentEdges (φ.vertex '' G.cluster ω x) ↔ e∈G.incidentEdges (G.cluster ω x) := by
    constructor
    · rintro ⟨z,⟨v,hv,rfl⟩,hz⟩
      exact ⟨v,hv,(hend v).mp hz⟩
    · rintro ⟨v,hv,hve⟩
      exact ⟨φ.vertex v,⟨v,hv,rfl⟩,(hend v).mpr hve⟩
  rw [hi]
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,φ.bondWeight]

lemma Aut.normalizedAbsoluteDiscrepancy (φ : G.Aut) (p : ℝ) (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p (φ.edge '' ω) (φ.vertex x) =
      G.normalizedAbsoluteDiscrepancy p ω x := by
  unfold CriticalPercolation.BondGraph.normalizedAbsoluteDiscrepancy
  rw [φ.weightedDiscrepancy,←φ.cluster_image,φ.modularMass_image]

lemma normalizedAbsoluteDiscrepancy_eq_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) {x y : V} (h : (G.openGraph ω).Reachable x y) :
    G.normalizedAbsoluteDiscrepancy p ω x = G.normalizedAbsoluteDiscrepancy p ω y := by
  unfold normalizedAbsoluteDiscrepancy
  rw [G.weightedDiscrepancy_change_base hc hl p ω x y h,abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg,ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (G.stabilizerWeight_ne_top x y),
    G.modularMass_change_base hc hl x y,G.cluster_eq_of_reachable h]
  exact ENNReal.mul_div_mul_left _ _ (G.stabilizerWeight_pos hc hl x y).ne'
    (G.stabilizerWeight_ne_top x y)

lemma normalizedAbsoluteDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p ω x ≤ (D*(2*K) : ℕ) := by
  unfold normalizedAbsoluteDiscrepancy
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [hm]
  · apply (ENNReal.div_le_iff (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm).mpr
    calc _ ≤ ENNReal.ofReal ((D*(2*K) : ℕ)*(G.modularMass x (G.cluster ω x)).toReal) :=
          ENNReal.ofReal_le_ofReal (G.abs_weightedDiscrepancy_le hc hl D K hD hK p hp ω x hm)
         _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_toReal hm]

lemma measurable_discrepancyVolumeBand [Countable V] [Countable E]
    (p : ℝ) (T U : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.discrepancyVolumeBand p T U ω x) := by
  exact (G.measurable_normalizedAbsoluteDiscrepancy p x).ite
    ((measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)).inter
      (measurableSet_lt (G.measurable_normalizedClusterVolume x) measurable_const)) measurable_const

lemma band_volume_ratio (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) :
    (G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)*G.clusterPeakRatio ω x =
      G.discrepancyVolumeBand p T U ω x := by
  unfold discrepancyVolumeBand
  split_ifs with h
  · have hne : G.clusterPeakRatio ω x≠0 := by
      intro he
      have hz : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,he]
      rw [hz] at h
      exact (not_le.mpr hT) h.1
    rw [normalizedClusterVolume,ite_eq_right hne,mul_assoc,
      ENNReal.inv_mul_cancel hne (ne_top_of_le_ne_top ENNReal.one_ne_top (G.clusterPeakRatio_le_one hc hl ω x)),mul_one]
  · simp

lemma band_volume_peak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) :
    (G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)*G.peakReturn ω x =
      ENNReal.ofReal |G.weightedDiscrepancy p ω x| *G.peakVolumeBand T U ω x := by
  by_cases h : T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U
  · by_cases hp : G.clusterPeak ω x
    · have hm : G.modularMass x (G.cluster ω x)≠∞ := by
        intro he
        have hz := G.clusterPeakRatio_eq_zero_of_heavy hc hl ω x he
        have hv : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,hz]
        rw [hv] at h
        exact (not_le.mpr hT) h.1
      rw [discrepancyVolumeBand,peakVolumeBand,ite_eq_left h,ite_eq_left h,
        G.normalizedClusterVolume_eq_at_peak hc hl ω x hp hm,normalizedAbsoluteDiscrepancy,
        ENNReal.div_mul_cancel (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm]
    · simp only [discrepancyVolumeBand,peakVolumeBand,ite_eq_left h,peakReturn,ite_eq_right hp,mul_zero]
  · simp only [discrepancyVolumeBand,peakVolumeBand,ite_eq_right h,zero_mul,mul_zero]

theorem expected_discrepancyBand_peak [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (T U : ℝ≥0∞) (hT : 0<T) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, G.discrepancyVolumeBand p T U ω x ∂G.law p) =
      ∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω,
        ENNReal.ofReal |G.weightedDiscrepancy p ω x| *G.peakVolumeBand T U ω x ∂G.law p := by
  have ht := G.expected_weighted_peakRatio hc hl hq p
    (fun ω x => G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)
    (fun x => (G.measurable_discrepancyVolumeBand p T U x).mul (G.measurable_normalizedClusterVolume x))
    (fun φ ω x => by
      simp only [discrepancyVolumeBand,φ.normalizedClusterVolume,φ.normalizedAbsoluteDiscrepancy])
    (fun ω x y h => by
      simp only [discrepancyVolumeBand,G.normalizedClusterVolume_eq_of_reachable ω h,
        G.normalizedAbsoluteDiscrepancy_eq_of_reachable hc hl p ω h])
  simpa only [G.band_volume_ratio hc hl p T U hT,G.band_volume_peak hc hl p T U hT] using ht

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedQuery
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace CriticalPercolation.SearchTree
open FiniteProduct

variable {E R : Type*}

lemma quadraticCost_nonneg (a : E → ℝ) (t : SearchTree E R) (ω : E → Prop) :
    0 ≤ t.quadraticCost a ω := by
  induction t with
  | done r => rfl
  | ask e l r hl hr =>
    simp only [quadraticCost]
    split_ifs <;> positivity

lemma takeQuadratic_sum_eq (a : E → ℝ) (p : ℝ) (t : SearchTree E R)
    (B : ℝ) (ω : E → Prop) (h : t.quadraticCost a ω ≤ B) :
    (t.takeQuadratic a B).weightedSum a p ω = t.weightedSum a p ω := by
  induction t generalizing B with
  | done r => rfl
  | ask e l r hl hr =>
    have ha : (a e)^2 ≤ B := by
      simp only [quadraticCost] at h
      split_ifs at h <;> linarith [quadraticCost_nonneg a l ω,quadraticCost_nonneg a r ω]
    simp only [takeQuadratic,ite_eq_left ha,weightedSum]
    split_ifs with he
    · rw [hr]
      simp only [quadraticCost,ite_eq_left he] at h
      linarith
    · rw [hl]
      simp only [quadraticCost,ite_eq_right he] at h
      linarith

lemma fourthPotential_step (x a B δ : ℝ) (hB : a^2≤B) (hδ : δ^2≤a^2) :
    (x+δ)^4 + 7*(B-a^2)*(x+δ)^2 + 5*(B-a^2)^2 ≤
      x^4+7*B*x^2+5*B^2+(4*x^3+14*(B-a^2)*x)*δ := by
  have h4 : δ^4≤a^4 := by nlinarith [sq_nonneg (δ^2-a^2),sq_nonneg δ,sq_nonneg a]
  have hxx := mul_le_mul_of_nonneg_left hδ (sq_nonneg x)
  have hb := mul_le_mul_of_nonneg_left hδ (sub_nonneg.mpr hB)
  have hba := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hB)
  nlinarith [sq_nonneg (x*δ-2*δ^2)]

variable [Fintype E] [DecidableEq E]

lemma expected_takeQuadratic_fourth_shift (a : E → ℝ) (t : SearchTree E R)
    (used : Finset E) (ht : t.Valid used) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (B : ℝ) (hB : 0≤B) (x : ℝ) :
    expect w (fun ω => (x+(t.takeQuadratic a B).weightedSum a p ω)^4) ≤
      x^4+7*B*x^2+5*B^2 := by
  induction t generalizing used w B x with
  | done r =>
    simp only [takeQuadratic,weightedSum,add_zero,expect_const w hw]
    nlinarith [sq_nonneg B,mul_nonneg hB (sq_nonneg x)]
  | ask e l r hl hr =>
    by_cases ha : (a e)^2≤B
    · have hB' : 0≤B-(a e)^2 := sub_nonneg.mpr ha
      have h0 := hl _ ht.2.1 (pin w e False) (pin_normalized w hw e False)
        (pin_nonneg w hn e False) (LazyDFS.fresh_pin w p used hf e False) _ hB' (x-a e*p)
      have h1 := hr _ ht.2.2 (pin w e True) (pin_normalized w hw e True)
        (pin_nonneg w hn e True) (LazyDFS.fresh_pin w p used hf e True) _ hB' (x+a e*(1-p))
      have he := hf e ht.1
      have hp0 : 0≤1-p^2 := by nlinarith [hp.1,hp.2]
      have hp1 : 0≤1-(1-p)^2 := by nlinarith [hp.1,hp.2]
      have hδ0 : (-a e*p)^2≤(a e)^2 := by
        nlinarith [mul_nonneg (sq_nonneg (a e)) hp0]
      have hδ1 : (a e*(1-p))^2≤(a e)^2 := by
        nlinarith [mul_nonneg (sq_nonneg (a e)) hp1]
      have g0 := fourthPotential_step x (a e) B (-a e*p) ha hδ0
      have g1 := fourthPotential_step x (a e) B (a e*(1-p)) ha hδ1
      have heq : (fun ω => (x+((.ask e l r : SearchTree E R).takeQuadratic a B).weightedSum a p ω)^4) =
          (fun ω => if ω e then ((x+a e*(1-p))+(r.takeQuadratic a (B-(a e)^2)).weightedSum a p ω)^4
            else ((x-a e*p)+(l.takeQuadratic a (B-(a e)^2)).weightedSum a p ω)^4) := by
        funext ω
        simp only [takeQuadratic,ite_eq_left ha,weightedSum]
        split_ifs <;> congr 1 <;> ring
      rw [heq]
      erw [expect_prop_ite]
      rw [he.1,he.2]
      have h0' := mul_le_mul_of_nonneg_left (h0.trans (by simpa only [sub_eq_add_neg,neg_mul] using g0))
        (sub_nonneg.mpr hp.2)
      have h1' := mul_le_mul_of_nonneg_left (h1.trans g1) hp.1
      nlinarith
    · simp only [takeQuadratic,ite_eq_right ha,weightedSum,add_zero,expect_const w hw]
      nlinarith [sq_nonneg B,mul_nonneg hB (sq_nonneg x)]

lemma expected_takeQuadratic_fourth (a : E → ℝ) (t : SearchTree E R)
    (used : Finset E) (ht : t.Valid used) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (B : ℝ) (hB : 0≤B) :
    expect w (fun ω => ((t.takeQuadratic a B).weightedSum a p ω)^4) ≤ 5*B^2 := by
  simpa using expected_takeQuadratic_fourth_shift a t used ht p hp w hw hn hf B hB 0

end CriticalPercolation.SearchTree
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedIncidenceSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

lemma compile_weighted_trace (G : BondGraph V E) (v : V) (n : ℕ) (st : State E)
    (ω : Set E) (a : E → ℝ) (p : ℝ) :
    let t := compile G v n st
    let out := t.run (fun e => decide (e∈ω))
    t.weightedSum a p ω + weightedRead a p ω st = weightedRead a p ω out ∧
    t.quadraticCost a ω + quadraticRead a st = quadraticRead a out := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.weightedSum,SearchTree.quadraticCost]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : e∉st.read := h.choose_spec.1
      have hopen := ih (st.open e)
      have hclosed := ih (st.closed e)
      have hs : weightedRead a p ω (st.open e) =
          (if e∈ω then a e*(1-p) else -a e*p)+weightedRead a p ω st := by
        simp only [weightedRead,State.open,Finset.sum_insert he]
      have hs' : weightedRead a p ω (st.closed e) =
          (if e∈ω then a e*(1-p) else -a e*p)+weightedRead a p ω st := by
        simp only [weightedRead,State.closed,Finset.sum_insert he]
      have hq : quadraticRead a (st.open e) = (a e)^2+quadraticRead a st := by
        simp only [quadraticRead,State.open,Finset.sum_insert he]
      have hq' : quadraticRead a (st.closed e) = (a e)^2+quadraticRead a st := by
        simp only [quadraticRead,State.closed,Finset.sum_insert he]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        (if ω e then a e*(1-p)+(compile G v n (st.open e)).weightedSum a p ω else
          -a e*p+(compile G v n (st.closed e)).weightedSum a p ω) + weightedRead a p ω st =
          weightedRead a p ω out ∧
        ((a e)^2 + if ω e then (compile G v n (st.open e)).quadraticCost a ω else
          (compile G v n (st.closed e)).quadraticCost a ω) + quadraticRead a st = quadraticRead a out)
      by_cases hω : e∈ω
      · have hω' : ω e := hω
        simp only [hω,hω',decide_true,if_true]
        dsimp only at hopen
        rw [hs,hq,ite_eq_left hω] at hopen
        constructor <;> linarith [hopen.1,hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,if_false]
        dsimp only at hclosed
        rw [hs',hq',ite_eq_right hω] at hclosed
        constructor <;> linarith [hclosed.1,hclosed.2]
    · simp [SearchTree.run,SearchTree.weightedSum,SearchTree.quadraticCost]

variable [Fintype E]

lemma tree_weighted (G : BondGraph V E) (v : V) (ω : Set E) (a : E → ℝ) (p : ℝ) :
    (tree G v).weightedSum a p ω = ∑ e, if e∈G.incidentEdges (G.cluster ω v) then
      (if e∈ω then a e*(1-p) else -a e*p) else 0 := by
  have h := (compile_weighted_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω a p).1
  change (tree G v).weightedSum a p ω + weightedRead a p ω ⟨∅,∅⟩ =
    weightedRead a p ω ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [weightedRead,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then
        (if e∈ω then a e*(1-p) else -a e*p) else 0 := by
      simp only [←Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [tree_mem_read]

lemma tree_quadratic (G : BondGraph V E) (v : V) (ω : Set E) (a : E → ℝ) :
    (tree G v).quadraticCost a ω = ∑ e,
      if e∈G.incidentEdges (G.cluster ω v) then (a e)^2 else 0 := by
  have h := (compile_weighted_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω a 0).2
  change (tree G v).quadraticCost a ω + quadraticRead a ⟨∅,∅⟩ =
    quadraticRead a ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [quadraticRead,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then (a e)^2 else 0 := by
      simp only [←Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [tree_mem_read]

end CriticalPercolation.IncidenceSearch
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedDiscrepancyLimit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedWeightedDiscrepancy_eq_tree (s : Set E) [Fintype s]
    (p : ℝ) (ω : Set E) (x : V) :
    G.restrictedWeightedDiscrepancy s p ω x =
      (IncidenceSearch.tree (G.restrictEdges s) x).weightedSum
        (fun e : s => (G.bondWeight x e.val).toReal) p (Subtype.val ⁻¹' ω) := by
  rw [IncidenceSearch.tree_weighted]
  unfold restrictedWeightedDiscrepancy restrictedWeightedTerm
  have ht : (∑' e : E, if e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x) then
      (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0) =
      ∑' e : s, if e.val∈G.incidentEdges (G.cluster (s∩ω) x) then
        (G.bondWeight x e.val).toReal*centeredCoefficient p ω e.val else 0 := by
    rw [tsum_subtype s (fun e : E => if e∈G.incidentEdges (G.cluster (s∩ω) x) then
      (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0)]
    apply tsum_congr
    intro e
    by_cases he : e∈s <;> simp only [Set.indicator,he,if_true,if_false,true_and,false_and]
  rw [ht,tsum_fintype]
  apply Finset.sum_congr rfl
  intro e _
  have hi : e∈(G.restrictEdges s).incidentEdges ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) ↔
      e.val∈G.incidentEdges (G.cluster (s∩ω) x) := by
    rw [FiniteClusters.restrict_cluster]
    rfl
  rw [hi]
  unfold centeredCoefficient
  simp only [Set.mem_preimage]
  split_ifs <;> ring

lemma norm_restrictedWeightedTerm_le (s : Set E) (p : ℝ) (hp : p∈Icc 0 1)
    (ω : Set E) (x : V) (e : E) :
    ‖G.restrictedWeightedTerm s p ω x e‖ ≤
      (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
  unfold restrictedWeightedTerm
  by_cases he : e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x)
  · have hi : e∈G.incidentEdges (G.cluster ω x) := by
      obtain ⟨v,hv,hve⟩ := he.2
      exact ⟨v,G.cluster_mono Set.inter_subset_right x hv,hve⟩
    rw [ite_eq_left he,ite_eq_left hi,Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_centeredCoefficient_le_one p hp ω e)
  · rw [ite_eq_right he,norm_zero]
    exact ENNReal.toReal_nonneg

lemma eventually_restrictedWeightedTerm (K : Set.FiniteExhaustion (Set.univ : Set E))
    (p : ℝ) (ω : Set E) (x : V) (e : E) :
    ∀ᶠ n in atTop, G.restrictedWeightedTerm (K n) p ω x e=G.weightedIncidenceTerm p ω x e := by
  by_cases he : e∈G.incidentEdges (G.cluster ω x)
  · obtain ⟨v,hv,hve⟩ := he
    obtain ⟨s,hs,hsω,hvs⟩ := G.mem_cluster_finite_witness hv
    obtain ⟨n,hn⟩ := finite_subset_exhaustion K (hs.insert e) (Set.subset_univ _)
    apply eventually_atTop.mpr
    refine ⟨n,fun m hm => ?_⟩
    have heK : e∈K m := K.mono hm (hn (Set.mem_insert e s))
    have hsK : s⊆K m := fun a ha => K.mono hm (hn (Set.mem_insert_of_mem e ha))
    have hem : e∈G.incidentEdges (G.cluster (K m∩ω) x) :=
      ⟨v,G.cluster_mono (Set.subset_inter hsK hsω) x hvs,hve⟩
    have hefull : e∈G.incidentEdges (G.cluster ω x) := ⟨v,hv,hve⟩
    simp only [restrictedWeightedTerm,weightedIncidenceTerm,heK,hem,hefull,true_and,if_true]
  · apply Eventually.of_forall
    intro n
    have hen : ¬(e∈K n ∧ e∈G.incidentEdges (G.cluster (K n∩ω) x)) := by
      rintro ⟨_,v,hv,hve⟩
      exact he ⟨v,G.cluster_mono Set.inter_subset_right x hv,hve⟩
    simp only [restrictedWeightedTerm,weightedIncidenceTerm,ite_eq_right hen,ite_eq_right he]

theorem tendsto_restrictedWeightedDiscrepancy (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1)
    (L : Set.FiniteExhaustion (Set.univ : Set E)) (ω : Set E) (x : V)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.restrictedWeightedDiscrepancy (L n) p ω x) atTop
      (𝓝 (G.weightedDiscrepancy p ω x)) := by
  apply tendsto_tsum_of_dominated_convergence
    (G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm)
  · intro e
    apply tendsto_const_nhds.congr'
    filter_upwards [G.eventually_restrictedWeightedTerm L p ω x e] with n hn
    exact hn.symm
  · exact Eventually.of_forall (fun n e => G.norm_restrictedWeightedTerm_le (L n) p hp ω x e)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedExplorationCost
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma bondWeight_le_of_clusterPeak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (ω : Set E) (x : V)
    (hp : G.clusterPeak ω x) {e : E} (he : e∈G.incidentEdges (G.cluster ω x)) :
    G.bondWeight x e ≤ (2*K : ℕ) := by
  obtain ⟨v,hv,hve⟩ := he
  exact (G.bondWeight_le_at_end hc hl K hK x v e hve).trans
    (by simpa only [mul_one] using mul_le_mul_right (hp v hv) (2*K : ℕ))

lemma restriction_incident_subset (s : Set E) (ω : Set E) (x : V) {e : s}
    (he : e∈(G.restrictEdges s).incidentEdges ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x)) :
    e.val∈G.incidentEdges (G.cluster ω x) := by
  obtain ⟨v,hv,hve⟩ := he
  refine ⟨v,?_,hve⟩
  rw [FiniteClusters.restrict_cluster] at hv
  exact G.cluster_mono Set.inter_subset_right x hv

lemma restriction_weighted_quadratic_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (s : Set E) [Fintype s]
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x) :
    ENNReal.ofReal ((IncidenceSearch.tree (G.restrictEdges s) x).quadraticCost
      (fun e : s => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω)) ≤
      (D*(2*K)^2 : ℕ)*G.modularMass x (G.cluster ω x) := by
  rw [IncidenceSearch.tree_quadratic,ENNReal.ofReal_sum_of_nonneg
    (fun e _ => by split_ifs <;> positivity)]
  have hsum : (∑ e : s, if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) ≤
      (D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x) := by
    calc
      _ ≤ ∑ e : s, if e.val∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e.val else 0 := by
        apply Finset.sum_le_sum
        intro e _
        split_ifs with he he'
        · rfl
        · exact False.elim (he' (G.restriction_incident_subset s ω x he))
        · exact zero_le
        · rfl
      _ ≤ ∑' e : E, if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0 := by
        change (∑ e : s, (fun e : E => if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0) e.val) ≤ _
        simpa only [tsum_fintype] using
          (ENNReal.tsum_comp_le_tsum_of_injective (f := (Subtype.val : s → E)) Subtype.val_injective
            (fun e : E => if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0))
      _ ≤ _ := G.weighted_incidence_le hc hl D K hD hK x _
  calc
    _ ≤ ∑ e : s, (2*K : ℕ)*(if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs with he
      · rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (G.bondWeight_ne_top x e.val),pow_two]
        exact mul_le_mul_left (G.bondWeight_le_of_clusterPeak hc hl K hK ω x hp
          (G.restriction_incident_subset s ω x he)) _
      · simp
    _ = (2*K : ℕ)*(∑ e : s, if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2*K : ℕ)*((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x)) := mul_le_mul_right hsum _
    _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow]; ring

lemma restriction_quadratic_real_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (s : Set E) [Fintype s]
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x)
    (U : ℝ) (hU : 0≤U) (hm : G.modularMass x (G.cluster ω x)≤ENNReal.ofReal U) :
    (IncidenceSearch.tree (G.restrictEdges s) x).quadraticCost
      (fun e : s => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω) ≤ (D*(2*K)^2 : ℕ)*U := by
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  calc _ ≤ (D*(2*K)^2 : ℕ)*G.modularMass x (G.cluster ω x) :=
        G.restriction_weighted_quadratic_le hc hl D K hD hK s ω x hp
       _ ≤ (D*(2*K)^2 : ℕ)*ENNReal.ofReal U := mul_le_mul_right hm _
       _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedIntegralBand
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CriticalPercolation
variable {X : Type*} [MeasurableSpace X]

lemma lintegral_fractional_fourth (μ : Measure X) (f h : X → ℝ≥0∞)
    (hf : AEMeasurable f μ) (hh : AEMeasurable h μ) (hh1 : ∀ x, h x≤1) :
    (∫⁻ x, f x*h x ∂μ)^4 ≤ (∫⁻ x, (f x)^4 ∂μ)*(∫⁻ x, h x ∂μ)^3 := by
  have hpq : (4:ℝ).HolderConjugate (4/3) := Real.holderConjugate_iff.mpr (by norm_num)
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hh
  have P : (∫⁻ x, h x^(4/3:ℝ) ∂μ) ≤ ∫⁻ x, h x ∂μ :=
    lintegral_mono (fun x => ENNReal.rpow_le_self_of_le_one (hh1 x) (by norm_num))
  have H' : (∫⁻ x, f x*h x ∂μ) ≤
      (∫⁻ x, (f x)^4 ∂μ)^(1/4:ℝ)*(∫⁻ x, h x ∂μ)^(3/4:ℝ) := by
    calc _ ≤ _ := H
         _ ≤ _ := by
           norm_num only [show (1/(4/3:ℝ))=3/4 by norm_num,ENNReal.rpow_ofNat]
           gcongr
  have H4 := ENNReal.rpow_le_rpow H' (by norm_num : (0:ℝ)≤4)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ)≤4),
    ←ENNReal.rpow_mul,←ENNReal.rpow_mul] at H4
  simpa only [show (1/4:ℝ)*4=1 by norm_num,show (3/4:ℝ)*4=3 by norm_num,
    ENNReal.rpow_one,ENNReal.rpow_ofNat] using H4

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedQueryLaw
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.SearchTree
variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma lintegral_takeQuadratic_fourth (a : E → ℝ) (t : SearchTree E R)
    (ht : t.Valid ∅) (p : unitInterval) (B : ℝ) (hB : 0≤B) :
    (∫⁻ ω : Set E, ENNReal.ofReal (|(t.takeQuadratic a B).weightedSum a p ω|)^4
      ∂BernoulliProduct.law (fun _ => p)) ≤ ENNReal.ofReal (5*B^2) := by
  have h0 (ω : Set E) : (|(t.takeQuadratic a B).weightedSum a p ω|)^4 =
      ((t.takeQuadratic a B).weightedSum a p ω)^4 := by rw [pow_abs,abs_of_nonneg (by positivity)]
  simp only [←ENNReal.ofReal_pow (abs_nonneg _),h0]
  rw [←ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (Filter.Eventually.of_forall (fun _ => by positivity)),BernoulliProduct.integral_law_eq_expect]
  apply ENNReal.ofReal_le_ofReal
  exact expected_takeQuadratic_fourth a t ∅ ht p p.2 _
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    (fun _ _ => ⟨by simp [BernoulliProduct.bitWeight],by simp [BernoulliProduct.bitWeight]⟩) B hB

end CriticalPercolation.SearchTree
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma lintegral_restrict (p : unitInterval) (s : Set E)
    (F : Set s → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω : Set E, F (Subtype.val ⁻¹' ω) ∂law (fun _ => p)) =
      ∫⁻ ω : Set s, F ω ∂law (fun _ => p) := by
  rw [←law_map_restrict (fun _ : E => p) s]
  exact (lintegral_map hF (Measurable.of_eval (fun edge => measurable_set_mem edge.val))).symm

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.SearchTree
variable {E R : Type*}

theorem restricted_weighted_event_fourth (s : Set E) [Fintype s] [DecidableEq s]
    (a : s → ℝ) (t : SearchTree s R) (ht : t.Valid ∅) (p : unitInterval)
    (B : ℝ) (hB : 0≤B) (h : Set E → ℝ≥0∞) (hm : Measurable h) (hh1 : ∀ ω, h ω≤1)
    (hcost : ∀ ω, h ω≠0 → t.quadraticCost a (Subtype.val ⁻¹' ω)≤B) :
    (∫⁻ ω : Set E, ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| *h ω
      ∂BernoulliProduct.law (fun _ => p))^4 ≤
      ENNReal.ofReal (5*B^2)*(∫⁻ ω, h ω ∂BernoulliProduct.law (fun _ => p))^3 := by
  let f : Set E → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p (Subtype.val ⁻¹' ω)|
  have hf0 : Measurable (fun η : Set s =>
      ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p η|) := measurable_of_finite _
  have hf : Measurable f := hf0.comp
    (Measurable.of_eval (fun edge : s => measurable_set_mem edge.val))
  have heq : (fun ω : Set E => ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| *h ω) =
      fun ω => f ω*h ω := by
    funext ω
    by_cases hh : h ω=0
    · simp [hh]
    · rw [show f ω= ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| by
        dsimp only [f]
        exact congrArg (fun z : ℝ => ENNReal.ofReal |z|)
          (t.takeQuadratic_sum_eq a p B (fun e => e.val∈ω) (hcost ω hh))]
  rw [heq]
  apply (CriticalPercolation.lintegral_fractional_fourth _ f h hf.aemeasurable hm.aemeasurable hh1).trans
  apply mul_le_mul_left
  change (∫⁻ ω : Set E, (ENNReal.ofReal
    |(t.takeQuadratic a B).weightedSum a p (Subtype.val ⁻¹' ω)|)^4
      ∂BernoulliProduct.law (fun _ => p)) ≤ _
  rw [BernoulliProduct.lintegral_restrict p s
    (fun η : Set s => (ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p η|)^4)
    (measurable_of_finite _)]
  exact lintegral_takeQuadratic_fourth a t ht p B hB

end CriticalPercolation.SearchTree
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedPeakBand
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] in
lemma measurable_restrictedWeightedDiscrepancy (s : Set E) [Fintype s] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.restrictedWeightedDiscrepancy s p ω x) := by
  simp only [G.restrictedWeightedDiscrepancy_eq_tree]
  exact (measurable_of_finite (fun η : Set s =>
    (IncidenceSearch.tree (G.restrictEdges s) x).weightedSum
      (fun e : s => (G.bondWeight x e.val).toReal) p η)).comp
    (Measurable.of_eval (fun edge : s => measurable_set_mem edge.val))

theorem expected_discrepancy_peakBand_fourth (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval)
    (T U : ℝ) (hT : 0<T) (hU : 0≤U) (x : V) :
    (∫⁻ ω, ENNReal.ofReal |G.weightedDiscrepancy p ω x| *
      G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p)^4 ≤
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*U)^2)*
        (∫⁻ ω, G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p)^3 := by
  classical
  let L := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let (n : ℕ) : Fintype (L n) := (L.finite n).fintype
  let h : Set E → ℝ≥0∞ := fun ω => G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x
  have hsupport (ω : Set E) (hh : h ω≠0) :=
    G.peakVolumeBand_support hc hl (ENNReal.ofReal T) (ENNReal.ofReal U)
      (ENNReal.ofReal_pos.mpr hT) ω x hh
  have hcost (n : ℕ) (ω : Set E) (hh : h ω≠0) :
      (IncidenceSearch.tree (G.restrictEdges (L n)) x).quadraticCost
        (fun e : L n => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω) ≤ (D*(2*K)^2 : ℕ)*U := by
    let := (L.finite n).fintype
    exact G.restriction_quadratic_real_le hc hl D K hD hK (L n) ω x
      (hsupport ω hh).1 U hU (hsupport ω hh).2.2.le
  let f : ℕ → Set E → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal |G.restrictedWeightedDiscrepancy (L n) p ω x| * h ω
  apply lintegral_fourth_bound_of_tendsto (G.law p) f
    (fun ω => ENNReal.ofReal |G.weightedDiscrepancy p ω x| * h ω) _
  · intro n
    let := (L.finite n).fintype
    exact (G.measurable_restrictedWeightedDiscrepancy (L n) p x).norm.ennreal_ofReal.mul
      (G.measurable_peakVolumeBand _ _ x)
  · intro ω
    by_cases hh : h ω=0
    · simpa only [f,hh,mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
    · have hm : G.modularMass x (G.cluster ω x)≠∞ :=
        ne_top_of_lt ((hsupport ω hh).2.2.trans_le (le_top))
      exact ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal
        ((G.tendsto_restrictedWeightedDiscrepancy hc hl D K hD hK p p.2 L ω x hm).abs))
        (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top (G.peakVolumeBand_le_one _ _ ω x)))
  · intro n
    let := (L.finite n).fintype
    have hn := @SearchTree.restricted_weighted_event_fourth E (IncidenceSearch.State (L n)) (L n) _ (Classical.decEq _)
      (fun e : L n => (G.bondWeight x e.val).toReal)
      (IncidenceSearch.tree (G.restrictEdges (L n)) x) (IncidenceSearch.tree_valid _ _) p
      ((D*(2*K)^2 : ℕ)*U) (by positivity) h (G.measurable_peakVolumeBand _ _ x)
      (fun ω => G.peakVolumeBand_le_one _ _ ω x) (hcost n)
    simpa only [f,G.restrictedWeightedDiscrepancy_eq_tree,BernoulliProduct.law_const,BondGraph.law] using hn

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_GeometricPeakBand
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
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma expected_peakBand_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (p : unitInterval) (T U : ℝ) (hT : 0<T)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p) ≤
      ENNReal.ofReal ((G.orbitRepresentatives hq).roots.card/T) := by
  rw [ENNReal.ofReal_div_of_pos hT,ENNReal.ofReal_natCast]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hT).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm]
  apply le_trans _ (G.expected_peakVolumeBand_mul_le hc hl hq p (ENNReal.ofReal T) (ENNReal.ofReal U))
  apply mul_le_mul_right
  exact Finset.single_le_sum (f := fun y => ∫⁻ ω,
    G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω y ∂G.law p)
    (fun _ _ => zero_le) hx

lemma expected_discrepancy_peakBand_geometric (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (n : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, ENNReal.ofReal |G.weightedDiscrepancy p ω x| *
      G.peakVolumeBand (ENNReal.ofReal ((16:ℝ)^n)) (ENNReal.ofReal ((16:ℝ)^(n+1))) ω x ∂G.law p) ≤
      ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
  let C : ℝ := (D*(2*K)^2 : ℕ)
  let N : ℝ := (G.orbitRepresentatives hq).roots.card
  have ht : (0:ℝ)<16^n := by positivity
  have h4 := G.expected_discrepancy_peakBand_fourth hc hl D K hD hK p
    ((16:ℝ)^n) ((16:ℝ)^(n+1)) ht (by positivity) x
  apply geometric_fourth_bound _ (5*(C*16)^2*N^3) (by dsimp [N]; positivity) n
  apply h4.trans
  calc
    _ ≤ ENNReal.ofReal (5*(C*(16:ℝ)^(n+1))^2)*
        (ENNReal.ofReal (N/(16:ℝ)^n))^3 := by
          apply mul_le_mul_right
          exact ENNReal.pow_le_pow_left (G.expected_peakBand_le hc hl hq p _ _ ht x hx)
    _ = ENNReal.ofReal ((5*(C*16)^2*N^3)/(16:ℝ)^n) := by
      rw [←ENNReal.ofReal_pow (by dsimp [N]; positivity),←ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_succ]
      field_simp
      ring

lemma expected_discrepancyBand_geometric (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (n : ℕ) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω,
      G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^n))
        (ENNReal.ofReal ((16:ℝ)^(n+1))) ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
  rw [G.expected_discrepancyBand_peak hc hl hq p _ _ (ENNReal.ofReal_pos.mpr (by positivity))]
  calc _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots,
      ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
          exact Finset.sum_le_sum (fun x hx => G.expected_discrepancy_peakBand_geometric hc hl hq D K hD hK p n x hx)
       _ = _ := by simp [nsmul_eq_mul]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_DiscrepancyTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators Topology

namespace CriticalPercolation

lemma ennreal_geometric_band (v : ℝ≥0∞) (hv : v≠∞) (N : ℕ)
    (hN : ENNReal.ofReal ((16:ℝ)^N)≤v) :
    ∃ m : ℕ, ENNReal.ofReal ((16:ℝ)^(N+m))≤v ∧ v<ENNReal.ofReal ((16:ℝ)^(N+m+1)) := by
  have hNr : (16:ℝ)^N≤v.toReal := (ENNReal.ofReal_le_iff_le_toReal hv).mp hN
  have hone : 1≤v.toReal := (one_le_pow₀ (by norm_num : (1:ℝ)≤16)).trans hNr
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hone (by norm_num : (1:ℝ)<16)
  have hNk : N≤k := by
    by_contra h
    have hkle : k+1≤N := by omega
    have hp : (16:ℝ)^(k+1)≤16^N := pow_le_pow_right₀ (by norm_num) hkle
    exact (not_lt_of_ge hNr) (hk'.trans_le hp)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hNk
  exact ⟨m,ENNReal.ofReal_le_of_le_toReal hk,(ENNReal.lt_ofReal_iff_toReal_lt hv).mpr hk'⟩

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma normalizedClusterVolume_ne_top (ω : Set E) (x : V) : G.normalizedClusterVolume ω x≠∞ := by
  unfold normalizedClusterVolume
  split_ifs with h
  · exact ENNReal.zero_ne_top
  · exact ENNReal.inv_ne_top.mpr h

lemma measurable_discrepancyVolumeTail (p : ℝ) (T : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.discrepancyVolumeTail p T ω x) :=
  (G.measurable_normalizedAbsoluteDiscrepancy p x).ite
    (measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)) measurable_const

omit [Countable V] [Countable E] in
lemma discrepancyVolumeTail_le_bands (p : ℝ) (N : ℕ) (ω : Set E) (x : V) :
    G.discrepancyVolumeTail p (ENNReal.ofReal ((16:ℝ)^N)) ω x ≤
      ∑' m : ℕ, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x := by
  unfold discrepancyVolumeTail
  split_ifs with h
  · obtain ⟨m,hm⟩ := ennreal_geometric_band _ (G.normalizedClusterVolume_ne_top ω x) N h
    calc
      _ = G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
          (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x := (ite_eq_left hm).symm
      _ ≤ _ := ENNReal.le_tsum (f := fun index : ℕ =>
        G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+index)))
          (ENNReal.ofReal ((16:ℝ)^(N+index+1))) ω x) m
  · exact zero_le

lemma expected_discrepancyTail_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (N : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, G.discrepancyVolumeTail p (ENNReal.ofReal ((16:ℝ)^N)) ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
          (ENNReal.ofReal (1/2:ℝ))^N*2 := by
  let A : ℝ := 5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1
  let R : ℝ≥0∞ := (G.orbitRepresentatives hq).roots.card
  calc
    _ ≤ ∫⁻ ω, ∑' m : ℕ, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x ∂G.law p :=
      lintegral_mono (fun ω => G.discrepancyVolumeTail_le_bands p N ω x)
    _ = ∑' m : ℕ, ∫⁻ ω, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x ∂G.law p :=
      lintegral_tsum (fun m => (G.measurable_discrepancyVolumeBand p _ _ x).aemeasurable)
    _ ≤ ∑' m : ℕ, R * ENNReal.ofReal (A*(1/2:ℝ)^(N+m)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      exact (Finset.single_le_sum (f := fun y => ∫⁻ ω,
        G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
          (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω y ∂G.law p) (fun _ _ => zero_le) hx).trans
        (G.expected_discrepancyBand_geometric hc hl hq D K hD hK p (N+m))
    _ = _ := by
      have he (m : ℕ) : ENNReal.ofReal (A*(1/2:ℝ)^(N+m)) =
          ENNReal.ofReal A * (ENNReal.ofReal (1/2:ℝ))^N * (ENNReal.ofReal (1/2:ℝ))^m := by
        rw [ENNReal.ofReal_mul (show 0≤A by dsimp [A]; positivity),
          ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),pow_add,mul_assoc]
      simp_rw [he,←mul_assoc]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      norm_num [R,A,ENNReal.ofReal_div_of_pos]

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_MonotoneBernoulli
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instNullSingletonClassRealUniform01 _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct

lemma uniform01_map_threshold (p : unitInterval) :
    Priority.uniform01.map (fun t : ℝ => t < p) = bitMeasure p := by
  have hm : Measurable (fun t : ℝ => t < p) := (measurable_id.lt measurable_const)
  have ht : Priority.uniform01 {t : ℝ | t < p} = ENNReal.ofReal p := by
    rw [Priority.uniform01,Measure.restrict_apply hm.setOf]
    have he : {t : ℝ | t < p} ∩ Icc 0 1 = Ico (0 : ℝ) (p : ℝ) := by
      ext t
      simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_Icc,Set.mem_Ico]
      exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,h.2.le.trans p.property.2⟩⟩
    rw [he,Real.volume_Ico,sub_zero]
  have htrue : (Priority.uniform01.map (fun t : ℝ => t < p)) {True} = bitMeasure p {True} := by
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun t : ℝ => t < p) ⁻¹' {True} = {t : ℝ | t < p} := by ext t; simp
    rw [he,ht]
    simp [bitMeasure,ENNReal.coe_nnreal_eq]
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b=True := propext (iff_true_intro hb)
    simpa only [he] using htrue
  · have he : b=False := propext (iff_false_intro hb)
    rw [he]
    have hcompl : ({True} : Set Prop)ᶜ = {False} := by ext a; simp
    rw [←hcompl,measure_compl (measurableSet_singleton _) (measure_ne_top _ _),
      measure_compl (measurableSet_singleton _) (measure_ne_top _ _),htrue,
      Measure.map_apply hm MeasurableSet.univ]
    simp

variable {E : Type*}

lemma measurable_atParameter (p : unitInterval) : Measurable (atParameter (E := E) p) :=
  Measurable.of_eval (fun edge => (measurable_pi_apply edge).lt measurable_const)

lemma markLaw_map_atParameter (p : unitInterval) :
    (markLaw (E := E)).map (atParameter p) = law (fun _ => p) := by
  have he : atParameter (E := E) p = MeasurableEquiv.setOfPred ∘ (fun u : E → ℝ => fun e => u e < p) := rfl
  rw [he,←Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    markLaw,Measure.infinitePi_map_pi (fun _ : E => Priority.uniform01)
      (f := fun _ : E => fun t : ℝ => t < (p : ℝ))
      (fun _ => measurable_id.lt measurable_const)]
  simp only [uniform01_map_threshold,law]

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyThinning
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_heavyFlag (p : unitInterval) (x : V) :
    Measurable (fun u => G.heavyFlag p u x) :=
  ((G.measurable_modularClusterMass x x).comp (measurable_atParameter p)).eq_const ∞

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma clusterPeakRatio_ne_zero_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    G.clusterPeakRatio ω x≠0 := by
  obtain ⟨y,hy⟩ := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω x hm
  rw [G.clusterPeakRatio_eq_inv_mass hc hl ω x y hm hy]
  exact ENNReal.inv_ne_zero.mpr (fun he => hm ((G.modularMass_eq_top_change_base hc hl x y _).mpr he))

omit [Countable V] [Countable E] in
lemma normalizedDiscrepancy_le_ratio_add_tail (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (T : ℝ≥0∞)
    (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p ω x ≤
      (D*(2*K) : ℕ)*T*G.clusterPeakRatio ω x + G.discrepancyVolumeTail p T ω x := by
  by_cases ht : T≤G.normalizedClusterVolume ω x
  · rw [discrepancyVolumeTail,ite_eq_left ht]
    exact le_add_left le_rfl
  · by_cases hm : G.modularMass x (G.cluster ω x)=∞
    · simp only [normalizedAbsoluteDiscrepancy,hm,ENNReal.div_top,zero_le]
    · have hr := G.clusterPeakRatio_ne_zero_of_mass_ne_top hc hl ω x hm
      have hr' := ne_top_of_le_ne_top ENNReal.one_ne_top (G.clusterPeakRatio_le_one hc hl ω x)
      have hv : G.normalizedClusterVolume ω x*G.clusterPeakRatio ω x=1 := by
        rw [normalizedClusterVolume,ite_eq_right hr,ENNReal.inv_mul_cancel hr hr']
      have hone : 1≤T*G.clusterPeakRatio ω x := by
        rw [←hv]
        exact mul_le_mul_left (le_of_not_ge ht) _
      calc _ ≤ ((D*(2*K) : ℕ) : ℝ≥0∞) := G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK p p.property ω x
           _ ≤ (D*(2*K) : ℕ)*T*G.clusterPeakRatio ω x := by
             simpa only [mul_one,mul_assoc] using mul_le_mul_right hone ((D*(2*K) : ℕ) : ℝ≥0∞)
           _ ≤ _ := le_add_right le_rfl

lemma expected_heavy_normalizedDiscrepancy_bound_bs_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p q : unitInterval) (N : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ u, if G.heavyFlag p u x then G.normalizedAbsoluteDiscrepancy q (atParameter q u) x else 0 ∂markLaw) ≤
      ((D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N)) *
        (∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 ∂markLaw) +
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
          (ENNReal.ofReal (1/2:ℝ))^N*2 := by
  let C : ℝ≥0∞ := (D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N)
  let r := fun u => if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0
  have hm : Measurable r := ((G.measurable_clusterPeakRatio x).comp (measurable_atParameter q)).ite
    (G.measurable_heavyFlag p x).setOf measurable_const
  calc
    _ ≤ ∫⁻ u, C*r u+G.discrepancyVolumeTail q (ENNReal.ofReal ((16:ℝ)^N)) (atParameter q u) x ∂markLaw := by
      apply lintegral_mono
      intro u
      by_cases h : G.heavyFlag p u x
      · simpa only [h,if_true,r,C] using G.normalizedDiscrepancy_le_ratio_add_tail hc hl D K hD hK q
          (ENNReal.ofReal ((16:ℝ)^N)) (atParameter q u) x
      · simp only [h,if_false,zero_le]
    _ = C*(∫⁻ u, r u ∂markLaw) + (∫⁻ ω, G.discrepancyVolumeTail q (ENNReal.ofReal ((16:ℝ)^N)) ω x ∂G.law q) := by
      rw [lintegral_add_left (show Measurable (fun u => C*r u) from measurable_const.mul hm),
        lintegral_const_mul'' C hm.aemeasurable]
      congr 1
      rw [show G.law q=(markLaw (E := E)).map (atParameter q) from by simpa only [BondGraph.law, BernoulliProduct.law_const] using (markLaw_map_atParameter (E := E) q).symm,
        lintegral_map (G.measurable_discrepancyVolumeTail q _ x) (measurable_atParameter q)]
    _ ≤ _ := add_le_add le_rfl (G.expected_discrepancyTail_bound hc hl hq D K hD hK q N x hx)

end BondGraph
end CriticalPercolation
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound_bs_oai.{u_1, u_2}
