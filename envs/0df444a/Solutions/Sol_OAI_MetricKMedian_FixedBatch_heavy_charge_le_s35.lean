-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.heavy_charge_le_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:01:35.934349+00:00
-- url     : https://prove2.me/submissions/0d2767e3-09ef-40a0-9313-7d8ec7f84062

import Mathlib
import Definitions.Def_OAIQ035K021
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
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

theorem B_nonneg (x : ℝ) : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg_s35 x)

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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_FixedBatchTransition
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_ChunkCharges
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
-- module Solutions.OAIQ035_KM.KMedian_Process_HeavyActions
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

theorem heavy_charge_le_s35_oai (G : I → Finset I) (H S : Finset I)
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

end MetricKMedian.FixedBatch
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.FixedBatch.heavy_charge_le_s35_oai.{u_1} := @OAI.MetricKMedian.FixedBatch.heavy_charge_le_s35_oai.{u_1}
