-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.masked_mass_sum_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:03:28.640107+00:00
-- url     : https://prove2.me/submissions/a6e3e24a-b204-44bb-b5dc-e5de540a76b6

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K021

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_ChunkCharges
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

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_UnbalancedActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

 theorem mass_eq_one_iff {g : ℝ} {Δ n : ℕ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) :
    g*(n:ℝ)=1 ↔ n=Δ := by
  rw [← hunit,mul_right_inj' (ne_of_gt hg)]
  exact Nat.cast_inj

 theorem heavy_inl_balanced (Full : Actions I I) (H : Finset I) (Δ : ℕ) {h : I}
    (hh : h ∉ H) : Sum.inl (⟨h,hh⟩ : {i : I // i ∉ H}) ∈
      balancedActions (heavyActions Full H) Δ ↔ (Full.erase h).card=Δ := by
  constructor
  · intro he
    exact (mem_filter.mp he).2
  · intro hc
    apply mem_filter.mpr
    exact ⟨(ordinary_heavyActions Full H _).mpr rfl,hc⟩

 theorem heavy_mass_fiber (Full : Actions I I) (H : Finset I) (g : ℝ) (h : I) :
    (∑ e ∈ univ.filter (fun e => heavyParent Full H e=h),
      mass g ((heavyActions Full H).erase e))=mass g (Full.erase h) := by
  have hh := (partition_alive_sums (univ.filter (fun e => heavyParent Full H e=h))
    (heavyActions Full H).erase (Full.erase h) univ
    (heavy_partition_disjoint Full H h) (heavy_partition_union Full H h) g (fun _ => 0)).1
  simpa only [univ_inter] using hh

theorem masked_mass_fiber (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) (h : I) :
    (∑ e ∈ univ.filter (fun e => heavyParent (graphActions G) H e=h),
      mass g (countErase (heavyActions (graphActions G) H) Δ e))=
    if mass g ((graphActions G).erase h)=1 then 0 else mass g ((graphActions G).erase h) := by
  by_cases hh : h ∈ H
  · have hn : mass g ((graphActions G).erase h) ≠ 1 := ne_of_gt (hH h hh)
    rw [ite_eq_right hn,← heavy_mass_fiber (graphActions G) H g h]
    apply sum_congr rfl
    intro e he
    have heh : heavyParent (graphActions G) H e ∈ H := (mem_filter.mp he).2 ▸ hh
    have ho : e ∉ (heavyActions (graphActions G) H).ordinary := by
      rw [ordinary_heavyActions]
      exact (heavyParent_membership _ _ _).mp heh
    have hb : e ∉ balancedActions (heavyActions (graphActions G) H) Δ :=
      fun hb => ho (mem_filter.mp hb).1
    rw [countErase,ite_eq_right hb]
  · rw [heavy_nonheavy_fiber (graphActions G) H hh,sum_singleton]
    have hb : Sum.inl (⟨h,hh⟩ : {i : I // i ∉ H}) ∈
        balancedActions (heavyActions (graphActions G) H) Δ ↔
        mass g ((graphActions G).erase h)=1 := by
      rw [heavy_inl_balanced (graphActions G) H Δ hh]
      exact (mass_eq_one_iff hg hunit).symm
    by_cases hm : mass g ((graphActions G).erase h)=1
    · rw [ite_eq_left hm,countErase,ite_eq_left (hb.mpr hm),mass,card_empty,Nat.cast_zero,mul_zero]
    · rw [ite_eq_right hm,countErase,ite_eq_right (fun he => hm (hb.mp he))]
      rfl

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential SourceBalance
variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem masked_mass_sum_s35_oai (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) :
    (∑ e, mass g (countErase (heavyActions (graphActions G) H) Δ e))=
      ∑ h ∈ nonzero (fun h => mass g ((graphActions G).erase h)), mass g ((graphActions G).erase h) := by
  rw [← sum_fiberwise univ (heavyParent (graphActions G) H)]
  simp_rw [masked_mass_fiber G H Δ hg hunit hH]
  rw [nonzero, sum_filter]
  apply sum_congr rfl
  intro h _
  split_ifs <;> simp_all

end MetricKMedian.FixedBatch
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.FixedBatch.masked_mass_sum_s35_oai.{u_1} := @OAI.MetricKMedian.FixedBatch.masked_mass_sum_s35_oai.{u_1}
