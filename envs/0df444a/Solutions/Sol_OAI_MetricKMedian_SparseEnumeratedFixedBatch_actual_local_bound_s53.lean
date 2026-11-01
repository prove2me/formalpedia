-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:33:02.908835+00:00
-- url     : https://prove2.me/submissions/8b6f0c32-619b-46e5-b010-5492146f0727

import Mathlib
import Definitions.Def_OAIQ053K033
import Definitions.Def_OAIQ053K039
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_forced_step_local_bound_s53
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_marginal_le_s53
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedFixedBatch_expected_step_bound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem mass_nonneg {g : ℝ} (hg : 0 ≤ g) (S : Finset I) : 0 ≤ mass g S := by
  exact mul_nonneg hg (Nat.cast_nonneg _)

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

theorem B_nonneg (x : ℝ) : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg_s53 x)

theorem chunks_le_full {C : Type*} (chunks : Finset C) (δ Y : C → ℝ)
    (a B V b : ℝ) (hδ : ∀ c ∈ chunks, 0 ≤ δ c)
    (hY : ∀ c ∈ chunks, 0 ≤ Y c) (hB : 0 ≤ B) :
    (∑ c ∈ chunks, (δ c * b - a * Y c - B * δ c * (V - Y c))) ≤
      (∑ c ∈ chunks, δ c) * b - a * (∑ c ∈ chunks, Y c) -
        B * (∑ c ∈ chunks, δ c) * (V - ∑ c ∈ chunks, Y c) := by
  have hpoint : ∀ c ∈ chunks, B * δ c * Y c ≤ B * δ c * (∑ t ∈ chunks, Y t) := by
    intro c hc
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hY hc) (mul_nonneg hB (hδ c hc))
  have hs := Finset.sum_le_sum hpoint
  have hrewrite : ∀ c, δ c * b - a * Y c - B * δ c * (V - Y c) =
      δ c * b - a * Y c - B * δ c * V + B * δ c * Y c := by intro c; ring
  simp_rw [hrewrite]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul] at hs ⊢
  nlinarith only [hs]

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_FixedBatchTransition
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_ChunkCharges
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem charge_eq_zero (D : Actions I E) (x g b : ℝ) (d : I → ℝ)
    (S : Finset I) {e : E} (he : e ∉ relevant D S) : charge D x g b d S e=0 := by
  have hn : ¬(e ∈ D.ordinary ∧ D.source e ∈ S) := fun h => he ((mem_relevant D S e).mpr (.inl h))
  have hi : S ∩ D.erase e=∅ := by
    apply not_nonempty_iff_eq_empty.mp
    exact fun h => he ((mem_relevant D S e).mpr (.inr h))
  simp only [charge, ite_eq_right hn, hi, mass, PhysicalPotential.cost, card_empty, Nat.cast_zero, mul_zero,
    sum_empty, zero_mul, sub_zero]

 theorem sum_charge_relevant (D : Actions I E) (x g b : ℝ) (d : I → ℝ) (S : Finset I) :
    (∑ e ∈ relevant D S, charge D x g b d S e)=∑ e, charge D x g b d S e := by
  apply sum_subset (subset_univ _)
  intro e _ he
  exact charge_eq_zero D x g b d S he

omit [DecidableEq E] [Fintype E] in
                                                                  
theorem partition_alive_sums (U : Finset E) (erase : E → Finset I) (full S : Finset I)
    (hp : (U : Set E).PairwiseDisjoint erase) (hu : U.biUnion erase=full)
    (g : ℝ) (d : I → ℝ) :
    (∑ e ∈ U, mass g (S ∩ erase e))=mass g (S ∩ full) ∧
    (∑ e ∈ U, PhysicalPotential.cost g d (S ∩ erase e))=PhysicalPotential.cost g d (S ∩ full) := by
  have hp' : (U : Set E).PairwiseDisjoint (fun e => S ∩ erase e) := by
    intro e he f hf hne
    exact (hp he hf hne).mono inter_subset_right inter_subset_right
  have hu' : U.biUnion (fun e => S ∩ erase e)=S ∩ full := by
    rw [← hu]
    ext i
    simp only [mem_biUnion, mem_inter]
    constructor
    · rintro ⟨e, he, hi, hie⟩
      exact ⟨hi, e, he, hie⟩
    · rintro ⟨hi, e, he, hie⟩
      exact ⟨e, he, hi, hie⟩
  constructor
  · simp only [mass, ← mul_sum]
    rw [← Nat.cast_sum, ← card_biUnion hp', hu']
  · exact (hu' ▸ sum_biUnion (f := fun i => g*d i) hp').symm

omit [Fintype E] [Fintype H] in

theorem external_chunks_le (D : Actions I E) (Full : Actions I H)
    (U : Finset E) (h : H) (x g b : ℝ) (d : I → ℝ) (S : Finset I)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hp : (U : Set E).PairwiseDisjoint D.erase) (hu : U.biUnion D.erase=Full.erase h)
    (hsource : ∀ e ∈ U, D.source e=Full.source h)
    (hext : ∀ e ∈ U, ¬(e ∈ D.ordinary ∧ D.source e ∈ S))
    (hfull : ¬(h ∈ Full.ordinary ∧ Full.source h ∈ S)) :
    (∑ e ∈ U, charge D x g b d S e) ≤ charge Full x g b d S h := by
  have heq : ∀ e ∈ U, charge D x g b d S e=
      mass g (S ∩ D.erase e)*min b (d (Full.source h))-
        coefficient x (mass g S)*PhysicalPotential.cost g d (S ∩ D.erase e)-
        B x*mass g (S ∩ D.erase e)*(PhysicalPotential.cost g d S-PhysicalPotential.cost g d (S ∩ D.erase e)) := by
    intro e he
    rw [charge, ite_eq_right (hext e he), hsource e he]
  rw [sum_congr rfl heq, charge, ite_eq_right hfull]
  obtain ⟨hm, hc⟩ := partition_alive_sums U D.erase (Full.erase h) S hp hu g d
  have hle := chunks_le_full U (fun e => mass g (S ∩ D.erase e))
    (fun e => PhysicalPotential.cost g d (S ∩ D.erase e))
    (coefficient x (mass g S)) (B x) (PhysicalPotential.cost g d S) (min b (d (Full.source h)))
    (fun e _ => mass_nonneg hg _) (fun e _ => cost_nonneg hg (fun i hi => hd i (mem_inter.mp hi).1))
    (B_nonneg x)
  simpa only [hm, hc] using hle

theorem split_actions_le (D : Actions I E) (Full : Actions I H) (parent : E → H)
    (x g b : ℝ) (d : I → ℝ) (S : Finset I)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hp : ∀ h, (↑(univ.filter (fun e => parent e=h)) : Set E).PairwiseDisjoint D.erase)
    (hu : ∀ h, (univ.filter (fun e => parent e=h)).biUnion D.erase=Full.erase h)
    (hsource : ∀ e, D.source e=Full.source (parent e))
    (hinside : ∀ e, (e ∈ D.ordinary ∧ D.source e ∈ S) ↔
      (parent e ∈ Full.ordinary ∧ Full.source (parent e) ∈ S))
    (hsingle : ∀ h, h ∈ Full.ordinary ∧ Full.source h ∈ S →
      ∃ e, univ.filter (fun e => parent e=h)={e}) :
    (∑ e ∈ relevant D S, charge D x g b d S e) ≤
      ∑ h ∈ relevant Full S, charge Full x g b d S h := by
  rw [sum_charge_relevant, sum_charge_relevant, ← sum_fiberwise univ parent]
  apply sum_le_sum
  intro h _
  by_cases hh : h ∈ Full.ordinary ∧ Full.source h ∈ S
  · obtain ⟨e, he⟩ := hsingle h hh
    have hmem : e ∈ univ.filter (fun e => parent e=h) := he ▸ mem_singleton_self e
    have hparent : parent e=h := (mem_filter.mp hmem).2
    have hsrc : D.source e=Full.source h := by rw [hsource, hparent]
    have herase : D.erase e=Full.erase h := by simpa only [he, singleton_biUnion] using hu h
    have hin : e ∈ D.ordinary ∧ D.source e ∈ S := (hinside e).mpr (hparent ▸ hh)
    rw [he, sum_singleton, charge, ite_eq_left hin, charge, ite_eq_left hh, hsrc, herase]
  · apply external_chunks_le D Full _ h x g b d S hg hd (hp h) (hu h)
    · intro e he
      rw [hsource, (mem_filter.mp he).2]
    · intro e he hin
      exact hh ((mem_filter.mp he).2 ▸ (hinside e).mp hin)
    · exact hh

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_FiniteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteGraph

variable {I H : Type*} [Fintype H] [DecidableEq I] [DecidableEq H]

theorem mem_touching (E : H → Finset I) (S : Finset I) (h : H) :
    h ∈ touching E S ↔ ∃ i ∈ S, i ∈ E h := by
  simp only [touching, Finset.mem_biUnion, incoming, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem touching_card (E : H → Finset I) (S : Finset I) {Δ : ℕ}
    (hin : ∀ i ∈ S, (incoming E i).card ≤ Δ) :
    (touching E S).card ≤ S.card*Δ := by
  apply le_trans (Finset.card_biUnion_le) ?_
  calc
    (∑ i ∈ S, (incoming E i).card) ≤ ∑ _i ∈ S, Δ := Finset.sum_le_sum hin
    _ = S.card*Δ := by simp

theorem self_not_conflict (E : H → Finset I) (balanced : Finset H) (h : H) :
    h ∉ conflicts E balanced h := by simp [conflicts]

theorem conflicts_card (E : H → Finset I) (balanced : Finset H) (h : H) {Δ : ℕ}
    (hout : (E h).card ≤ Δ) (hin : ∀ i ∈ E h, (incoming E i).card ≤ Δ) :
    (conflicts E balanced h).card ≤ Δ^2 := by
  have hsub : conflicts E balanced h ⊆ touching E (E h) :=
    Finset.Subset.trans (Finset.erase_subset _ _) Finset.inter_subset_left
  calc
    (conflicts E balanced h).card ≤ (touching E (E h)).card := Finset.card_le_card hsub
    _ ≤ (E h).card*Δ := touching_card E (E h) hin
    _ ≤ Δ*Δ := Nat.mul_le_mul_right Δ hout
    _ = Δ^2 := (pow_two Δ).symm

end MetricKMedian.FiniteGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_ActionDegrees
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem relevant_card_bound (D : Actions I E) (S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ)
    (hsource : (D.ordinary : Set E).InjOn D.source)
    (hin : ∀ i ∈ S, (FiniteGraph.incoming D.erase i).card ≤ Δ) :
    (relevant D S).card ≤ Δ^2+Δ := by
  let U := D.ordinary.filter (fun e => D.source e ∈ S)
  have hU : U.card ≤ S.card := by
    apply card_le_card_of_injOn D.source
    · intro e he
      exact (mem_filter.mp he).2
    · intro e he f hf hef
      exact hsource (mem_filter.mp he).1 (mem_filter.mp hf).1 hef
  have heq : relevant D S=U ∪ FiniteGraph.touching D.erase S := by
    ext e
    simp only [mem_relevant, mem_union, U, mem_filter, FiniteGraph.mem_touching,
      nonempty_def, mem_inter]
  rw [heq]
  calc
    _ ≤ U.card+(FiniteGraph.touching D.erase S).card := card_union_le _ _
    _ ≤ S.card+S.card*Δ := Nat.add_le_add hU (FiniteGraph.touching_card _ _ hin)
    _ ≤ Δ+Δ*Δ := Nat.add_le_add hS (Nat.mul_le_mul_right Δ hS)
    _ = Δ^2+Δ := by ring

omit [DecidableEq I] in
                                                                        
theorem card_le_grid {g : ℝ} {Δ : ℕ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (S : Finset I) (hm : mass g S ≤ 1) : S.card ≤ Δ := by
  have hreal : (S.card:ℝ) ≤ (Δ:ℝ) := by
    apply (mul_le_mul_iff_right₀ hg).mp
    simpa only [mass, hunit] using hm
  exact_mod_cast hreal

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_SourceGenerator
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic GeneratorAverage GraphMoments
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem mem_graph_erase (G : I → Finset I) (h i : I) :
    i ∈ (graphActions G).erase h ↔ h ∈ G i := by simp [graphActions]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_HeavyActions
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem ordinary_heavyActions (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    e ∈ (heavyActions Full H).ordinary ↔ e.isLeft := by simp [heavyActions]

omit [Fintype I] in
 theorem heavyParent_membership (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    heavyParent Full H e ∈ H ↔ ¬ e.isLeft := by
  cases e with
  | inl h => simp [heavyParent, h.property]
  | inr p => simp [heavyParent, p.property.1]

 theorem same_parent_eraser (Full : Actions I I) (H : Finset I)
    (e f : HeavyAction Full H) {i : I}
    (hpar : heavyParent Full H e=heavyParent Full H f)
    (he : i ∈ (heavyActions Full H).erase e) (hf : i ∈ (heavyActions Full H).erase f) : e=f := by
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (Subtype.ext hpar)
    | inr f =>
      change e.val=f.val.1 at hpar
      exact (e.property (hpar.symm ▸ f.property.1)).elim
  | inr e =>
    cases f with
    | inl f =>
      change e.val.1=f.val at hpar
      exact (f.property (hpar ▸ e.property.1)).elim
    | inr f =>
      have he' : i=e.val.2 := mem_singleton.mp he
      have hf' : i=f.val.2 := mem_singleton.mp hf
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hpar (he'.symm.trans hf')))

 theorem heavy_partition_disjoint (Full : Actions I I) (H : Finset I) (h : I) :
    (↑(univ.filter (fun e => heavyParent Full H e=h)) : Set (HeavyAction Full H)).PairwiseDisjoint
      (heavyActions Full H).erase := by
  intro e he f hf hne
  apply disjoint_left.mpr
  intro i hie hif
  exact hne (same_parent_eraser Full H e f
    ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm) hie hif)

 theorem heavy_partition_union (Full : Actions I I) (H : Finset I) (h : I) :
    (univ.filter (fun e => heavyParent Full H e=h)).biUnion (heavyActions Full H).erase=Full.erase h := by
  ext i
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hi⟩
    cases e with
    | inl e => exact he ▸ hi
    | inr e =>
      change e.val.1=h at he
      have hi' : i=e.val.2 := mem_singleton.mp hi
      exact he ▸ (hi'.symm ▸ e.property.2)
  · intro hi
    by_cases hh : h ∈ H
    · exact ⟨.inr ⟨(h,i), hh, hi⟩, rfl, mem_singleton_self _⟩
    · exact ⟨.inl ⟨h,hh⟩, rfl, hi⟩

 theorem heavy_nonheavy_fiber (Full : Actions I I) (H : Finset I) {h : I} (hh : h ∉ H) :
    univ.filter (fun e => heavyParent Full H e=h)=({Sum.inl ⟨h,hh⟩} : Finset (HeavyAction Full H)) := by
  classical
  apply Finset.ext
  intro e
  rw [Finset.mem_singleton]
  simp only [mem_filter, mem_univ, true_and]
  cases e with
  | inl e => simp only [heavyParent, Sum.inl.injEq, Subtype.ext_iff]
  | inr e =>
    constructor
    · intro he
      change e.val.1=h at he
      exact (hh (he ▸ e.property.1)).elim
    · intro he
      cases he

theorem heavy_charge_le (G : I → Finset I) (H S : Finset I)
    (hHS : Disjoint H S) (x g b : ℝ) (d : I → ℝ)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i) :
    (∑ e ∈ relevant (heavyActions (graphActions G) H) S,
      charge (heavyActions (graphActions G) H) x g b d S e) ≤
    ∑ h ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S h := by
  apply split_actions_le _ _ (heavyParent (graphActions G) H) x g b d S hg hd
    (heavy_partition_disjoint _ _) (heavy_partition_union _ _) (fun _ => rfl)
  · intro e
    rw [ordinary_heavyActions]
    constructor
    · rintro ⟨_, hs⟩
      exact ⟨mem_univ _, hs⟩
    · rintro ⟨_, hs⟩
      refine ⟨?_, hs⟩
      by_contra he
      exact disjoint_left.mp hHS ((heavyParent_membership _ _ e).mpr he) hs
  · intro h hh
    have hn : h ∉ H := fun he => disjoint_left.mp hHS he hh.2
    exact ⟨_, heavy_nonheavy_fiber _ _ hn⟩

 theorem heavy_ordinary_injective (G : I → Finset I) (H : Finset I) :
    Set.InjOn (heavyActions (graphActions G) H).source
      (↑(heavyActions (graphActions G) H).ordinary : Set (HeavyAction (graphActions G) H)) := by
  intro e he f hf hpar
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (Subtype.ext hpar)
    | inr f => simp [heavyActions] at hf
  | inr e => simp [heavyActions] at he

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_ActualActions
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

omit [Fintype I] in
 theorem balancedConflicts_bound (D : Actions I E) (Δ : ℕ)
    (hin : ∀ i, (incoming D.erase i).card ≤ Δ) (e : E) :
    (balancedConflicts D Δ e).card ≤ Δ^2 := by
  unfold balancedConflicts
  split_ifs with he
  · apply conflicts_card _ _ _ (le_of_eq (mem_filter.mp he).2)
    intro i _
    exact hin i
  · simp

omit [Fintype I] in
 theorem balancedConflicts_self (D : Actions I E) (Δ : ℕ) (e : E) :
    e ∉ balancedConflicts D Δ e := by
  unfold balancedConflicts
  split_ifs
  · exact self_not_conflict _ _ _
  · simp

theorem heavy_incoming_card (G : I → Finset I) (H : Finset I) (i : I) :
    (incoming (heavyActions (graphActions G) H).erase i).card=(G i).card := by
  apply card_bij (fun e _ => heavyParent (graphActions G) H e)
  · intro e he
    have hi := (mem_filter.mp he).2
    have hu := heavy_partition_union (graphActions G) H (heavyParent (graphActions G) H e)
    have hic : i ∈ (graphActions G).erase (heavyParent (graphActions G) H e) := by
      rw [← hu]
      exact mem_biUnion.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,rfl⟩,hi⟩
    exact (mem_graph_erase _ _ _).mp hic
  · intro e he f hf heq
    exact same_parent_eraser (graphActions G) H e f heq (mem_filter.mp he).2 (mem_filter.mp hf).2
  · intro h hh
    have hh' := (mem_graph_erase G h i).mpr hh
    rw [← heavy_partition_union (graphActions G) H h] at hh'
    obtain ⟨e,he,hi⟩ := mem_biUnion.mp hh'
    exact ⟨e,mem_filter.mpr ⟨mem_univ _,hi⟩,(mem_filter.mp he).2⟩

 theorem full_incoming_card (G : I → Finset I) (i : I) :
    (incoming (graphActions G).erase i).card=(G i).card := by
  congr 1
  ext h
  simp [incoming,mem_graph_erase]

 theorem heavy_relevant_bound (G : I → Finset I) (H S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ) (hG : ∀ i, (G i).card=Δ) :
    (relevant (heavyActions (graphActions G) H) S).card ≤ Δ^2+Δ := by
  apply relevant_card_bound _ _ hS (heavy_ordinary_injective G H)
  intro i _
  exact le_of_eq ((heavy_incoming_card G H i).trans (hG i))

 theorem full_relevant_bound (G : I → Finset I) (S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ) (hG : ∀ i, (G i).card=Δ) :
    (relevant (graphActions G) S).card ≤ Δ^2+Δ := by
  apply relevant_card_bound _ _ hS (fun _ _ _ _ h => h)
  intro i _
  exact le_of_eq ((full_incoming_card G i).trans (hG i))

 theorem nonordinary_parent_heavy (G : I → Finset I) (H : Finset I)
    (e : HeavyAction (graphActions G) H) (he : e ∉ (heavyActions (graphActions G) H).ordinary) :
    (heavyActions (graphActions G) H).source e ∈ H := by
  apply (heavyParent_membership _ _ e).mpr
  simpa only [ordinary_heavyActions] using he

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

 theorem batchConstant_nonneg (Δ : ℕ) : 0 ≤ batchConstant Δ := by
  unfold batchConstant
  positivity

theorem uniform_remainder (Δ n o : ℕ) {h g φ R : ℝ}
    (hn : n ≤ Δ^2+Δ) (ho : o ≤ n^2)
    (hh : 0 ≤ h) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hφ : 0 ≤ φ) (hR : 0 ≤ R) :
    R*(16*(n:ℝ)*((Δ^2:ℕ):ℝ)*h^2*g^2+8*(n:ℝ)*φ*h*g+
      256*(o:ℝ)*h^2*g^2+6*h^2+8*(n:ℝ)*h^2*g) ≤
      batchConstant Δ*h*(φ+h)*R := by
  let N : ℝ := Δ^2+Δ
  have hn' : (n:ℝ) ≤ N := by dsimp only [N]; exact_mod_cast hn
  have ho' : (o:ℝ) ≤ N^2 := by
    have h := ho.trans (Nat.pow_le_pow_left hn 2)
    dsimp only [N]
    exact_mod_cast h
  have hn0 : 0 ≤ N := by dsimp [N]; positivity
  have hg2 : g^2 ≤ 1 := by nlinarith only [hg0,hg1]
  have t1 : 16*(n:ℝ)*((Δ^2:ℕ):ℝ)*h^2*g^2 ≤ 16*N*(Δ:ℝ)^2*h^2 := by
    have a : 16*(n:ℝ)*((Δ^2:ℕ):ℝ)*h^2 ≤ 16*N*(Δ:ℝ)^2*h^2 := by
      rw [Nat.cast_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn' (by norm_num)) (sq_nonneg (Δ:ℝ))) (sq_nonneg h)
    exact (mul_le_of_le_one_right (by positivity) hg2).trans a
  have t2 : 8*(n:ℝ)*φ*h*g ≤ 8*N*φ*h := by
    exact (mul_le_of_le_one_right (by positivity) hg1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn' (by norm_num)) hφ) hh)
  have t3 : 256*(o:ℝ)*h^2*g^2 ≤ 256*N^2*h^2 := by
    exact (mul_le_of_le_one_right (by positivity) hg2).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ho' (by norm_num)) (sq_nonneg h))
  have t4 : 8*(n:ℝ)*h^2*g ≤ 8*N*h^2 := by
    exact (mul_le_of_le_one_right (by positivity) hg1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn' (by norm_num)) (sq_nonneg h))
  have hrem : 0 ≤ (16*N*(Δ:ℝ)^2+256*N^2+8*N+6)*φ*h+8*N*h^2 := by positivity
  have hs : 16*(n:ℝ)*((Δ^2:ℕ):ℝ)*h^2*g^2+8*(n:ℝ)*φ*h*g+
      256*(o:ℝ)*h^2*g^2+6*h^2+8*(n:ℝ)*h^2*g ≤ batchConstant Δ*h*(φ+h) := by
    change _ ≤ (16*N*(Δ:ℝ)^2+256*N^2+16*N+6)*h*(φ+h)
    nlinarith only [t1,t2,t3,t4,hrem]
  nlinarith only [mul_le_mul_of_nonneg_left hs hR]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseLocalBatch
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedFixedBatch
open Finset PhysicalPotential Analytic FixedBatch
variable {I : Type} [DecidableEq I] [Fintype I] {n : ℕ}

theorem actual_local_bound_s53_oai (G : I → Finset I) (H S F : Finset I) (Δ : ℕ)
    (enum : Fin n ≃ HeavyAction (graphActions G) H)
    (p : ℚ) (q : HeavyAction (graphActions G) H → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1) {x g h φ R b b' : ℝ} (d : I → ℝ)
    (hprob : (p:ℝ)=2*h*g)
    (hG : ∀ i, (G i).card=Δ) (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*(p:ℝ))
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hy : mass g S ≤ 1) (hF : F ⊆ S) (hHS : H ∩ S ⊆ F)
    (hd0 : ∀ i, 0 ≤ d i) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S, d i ≤ R)
    (hbQ : b ≤ 5*((PhysicalPotential.cost g d S+(1-mass g S)*b)/g))
    (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) (hb'0 : 0 ≤ b') (hb' : b' ≤ b)
    (hbF : ∀ i ∈ F, b' ≤ d i) (hbH : ∀ i ∈ H, b' ≤ d i) :
    let D := heavyActions (graphActions G) H
    let μ := (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ)
      p q hp hq0).real
    μ.expect (fun A => potential (x*Real.exp (-h)) g d
      (nextAliveAt D (coefficient x (mass g S)) d (S \ F) A)
      (nextCap D d b' A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S e))+
      batchConstant Δ*h*(φ+h)*R := by
  intro D μ
  have hcard : S.card ≤ Δ := card_le_grid hg hunit S hy
  have hin : ∀ i, (FiniteGraph.incoming D.erase i).card ≤ Δ :=
    fun i => le_of_eq ((heavy_incoming_card G H i).trans (hG i))
  have hD := heavy_relevant_bound G H S hcard hG
  have hFull := full_relevant_bound G S hcard hG
  have hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g := by
    intro e _
    have hpQ : (p:ℝ) ≤ 4*h*g := by rw [hprob]; nlinarith only [mul_nonneg hh0 hg.le]
    have hqQ : ∀ e, (q e:ℝ) ≤ 4*h*g := by
      intro e
      have he := mul_le_mul_of_nonneg_right hφ1 (show 0 ≤ 2*h*g by positivity)
      have heq := (hq e).2
      rw [hprob] at heq
      linarith only [he,heq]
    have he := SparseEnumeratedBatch.marginal_le_s53 enum (balancedActions D Δ) (balancedConflicts D Δ)
      p q hp hq0 hpQ hqQ e
    change μ.prob _ ≤ _ at he
    linarith only [he]
  by_cases hFn : F.Nonempty
  · have hδ : g ≤ mass g F := by
      unfold mass
      have hf : (1:ℝ) ≤ F.card := by exact_mod_cast hFn.card_pos
      nlinarith only [mul_le_mul_of_nonneg_left hf hg.le]
    have hh := forced_step_local_bound_s53 D (graphActions G) μ d S F hx0 hx1 hg hg1 hh0 hh1
      hsmall hy hF hδ hd0 hb0 hbQ hb'0 hb' hbF hD hFull hmarg
    exact hh.trans (le_add_of_nonneg_right (by positivity [batchConstant_nonneg Δ]))
  · have hFe : F=∅ := not_nonempty_iff_eq_empty.mp hFn
    have hdis : Disjoint H S := by
      apply disjoint_left.mpr
      intro i hi hs
      have he := hHS (mem_inter.mpr ⟨hi,hs⟩)
      simp [hFe] at he
    have hheavy : ∀ e, e ∉ D.ordinary → b' ≤ d (D.source e) :=
      fun e he => hbH _ (nonordinary_parent_heavy G H e he)
    have hb := expected_step_bound_s53 enum D (balancedActions D Δ) (balancedConflicts D Δ) p q hp hq0
      hprob hh0 hg.le hφ0 hφ1 hq (balancedConflicts_bound D Δ hin)
      (balancedConflicts_self D Δ) d S hx0 hx1 hR0 hd0 hdR
      hy hb0 hbR hb'0 hb' hheavy
    have hc := heavy_charge_le G H S hdis x g b d hg.le (fun i _ => hd0 i)
    have hcm := mul_le_mul_of_nonneg_left hc (mul_nonneg hh0 hg.le)
    have ho : (univ : Finset (relevant D S)).offDiag.card ≤ (relevant D S).card^2 := by
      rw [offDiag_card]
      simp only [card_univ,Fintype.card_coe]
      exact (Nat.sub_le _ _).trans_eq (pow_two _).symm
    have hr := uniform_remainder Δ (relevant D S).card
      (univ : Finset (relevant D S)).offDiag.card hD ho hh0 hg.le hg1 hφ0 hR0
    simp only [hFe,sdiff_empty]
    change μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAlive D x g d S A)
      (nextCap D d b' A)-potential x g d S b) ≤ _
    change μ.expect _ ≤ _ at hb
    nlinarith only [hb,hcm,hr]

end MetricKMedian.SparseEnumeratedFixedBatch
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53_oai := @OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53_oai
