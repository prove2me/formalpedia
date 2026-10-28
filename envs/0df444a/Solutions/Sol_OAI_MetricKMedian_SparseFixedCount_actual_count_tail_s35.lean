-- Prove2me | solution 1 for OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:30:33.338979+00:00
-- url     : https://prove2.me/submissions/294514ed-5bca-4795-823f-f62f43fe5115

import Mathlib
import Definitions.Def_OAIQ035K049
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_count_action_size_s35
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_masked_biased_linear_bound_s35
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_masked_mass_sum_s35
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_masked_total_bound_s35
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBernoulli_conditional_count_tail_s35

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

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceGenerator
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

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActualActions
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

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountGeometry
open Finset
variable {E U : Type*} [Fintype E] [DecidableEq E] [DecidableEq U]

omit [Fintype E] in
theorem overlap_self (S : E → Finset U) (e : E) : overlap S e e=0 := by simp [overlap]
omit [Fintype E] in
theorem overlap_symm (S : E → Finset U) (e f : E) : overlap S e f=overlap S f e := by
  by_cases h : e=f
  · subst f; rfl
  · simp only [overlap, ite_eq_right h, ite_eq_right (Ne.symm h), inter_comm]

theorem overlap_row_bound (S : E → Finset U) {D : ℕ}
    (hdegree : ∀ u, (univ.filter (fun e => u ∈ S e)).card ≤ D) (e : E) :
    (∑ f, overlap S e f) ≤ (D-1)*(S e).card := by
  have hpoint : ∀ f, overlap S e f = ∑ u ∈ S e, if f ≠ e ∧ u ∈ S f then (1:ℕ) else 0 := by
    intro f
    rw [sum_boole]
    by_cases h : e=f
    · subst f; simp [overlap]
    · simp only [overlap, ite_eq_right h]
      congr 1
      ext u
      simp only [mem_inter, mem_filter]
      constructor
      · intro hu; exact ⟨hu.1, Ne.symm h, hu.2⟩
      · intro hu; exact ⟨hu.1, hu.2.2⟩
  simp_rw [hpoint]
  rw [sum_comm]
  calc
    (∑ u ∈ S e, ∑ f, if f ≠ e ∧ u ∈ S f then (1:ℕ) else 0) ≤ ∑ _u ∈ S e, (D-1) := by
      apply sum_le_sum
      intro u hu
      rw [sum_boole]
      have he : e ∈ univ.filter (fun f => u ∈ S f) := by simp [hu]
      have hfilter : univ.filter (fun f => f ≠ e ∧ u ∈ S f) =
          (univ.filter (fun f => u ∈ S f)).erase e := by
        ext f
        simp only [mem_filter, mem_univ, true_and, mem_erase]
      rw [hfilter, card_erase_of_mem he]
      exact Nat.sub_le_sub_right (hdegree u) 1
    _ = _ := by simp only [sum_const, smul_eq_mul]; exact Nat.mul_comm _ _

theorem scaled_overlap_row_bound (S : E → Finset U) {D : ℕ} {g : ℝ}
    (hg : 0 ≤ g) (hD : 1 ≤ D)
    (hdegree : ∀ u, (univ.filter (fun e => u ∈ S e)).card ≤ D) (e : E) :
    (∑ f, g*(overlap S e f : ℝ)) ≤ ((D:ℝ)-1)*(g*(S e).card) := by
  rw [← mul_sum]
  have h := overlap_row_bound S hdegree e
  have hr : (∑ f, (overlap S e f:ℝ)) ≤ ((D:ℝ)-1)*(S e).card := by
    have hh : (∑ f, (overlap S e f:ℝ)) ≤ ((D-1:ℕ):ℝ)*(S e).card := by exact_mod_cast h
    simpa only [Nat.cast_sub hD, Nat.cast_one] using hh
  nlinarith only [mul_le_mul_of_nonneg_left hr hg]

end MetricKMedian.CountGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SourceBalance
open Finset
variable {I : Type*} [Fintype I]

 theorem amount_eq_negative (m : I → ℝ) (hm : ∑ i, m i=Fintype.card I) :
    amount m=∑ i ∈ negative m, (m i-1) := by
  have hzero : (∑ i, (1-m i))=0 := by rw [sum_sub_distrib,hm]; simp
  have hp : ∀ i, max (1-m i) 0-max (m i-1) 0=1-m i := by
    intro i
    by_cases h : m i ≤ 1
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right (by linarith only [h]),max_eq_left (by linarith only [h])]
      ring
  have hs := congrArg (fun f : I → ℝ => ∑ i, f i) (funext hp)
  simp only [sum_sub_distrib,hzero] at hs
  rw [amount,negative,sum_filter]
  have he : (∑ i, max (m i-1) 0)=∑ i, if 1 < m i then m i-1 else 0 := by
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · exact max_eq_left (sub_nonneg.mpr hi.le)
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hi))
  linarith only [hs,he]

 theorem abs_sum (m : I → ℝ) (hm : ∑ i, m i=Fintype.card I) :
    (∑ i, |1-m i|)=2*amount m := by
  have hp : ∀ i, |1-m i|=max (1-m i) 0+max (m i-1) 0 := by
    intro i
    by_cases h : m i ≤ 1
    · rw [abs_of_nonneg (sub_nonneg.mpr h),max_eq_left (sub_nonneg.mpr h),
        max_eq_right (sub_nonpos.mpr h),add_zero]
    · rw [abs_of_nonpos (by linarith only [h]),max_eq_right (by linarith only [h]),
        max_eq_left (by linarith only [h]),zero_add]
      ring
  simp_rw [hp]
  rw [sum_add_distrib]
  have hn : (∑ i, max (m i-1) 0)=amount m := by
    rw [amount_eq_negative m hm,negative,sum_filter]
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · exact max_eq_left (sub_nonneg.mpr hi.le)
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hi))
  rw [hn]
  change amount m+amount m=2*amount m
  ring

 theorem nonzero_card (m : I → ℝ) {g : ℝ} (hm : ∑ i, m i=Fintype.card I)
    (hgrid : ∀ i, m i ≠ 1 → g ≤ |1-m i|) :
    g*((nonzero m).card:ℝ) ≤ 2*amount m := by
  have hsum := sum_le_sum (s := nonzero m) (f := fun _ => g) (g := fun i => |1-m i|)
    (fun i hi => hgrid i (mem_filter.mp hi).2)
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hle := sum_le_univ_sum_of_nonneg (s := nonzero m) (fun i => abs_nonneg (1-m i))
  rw [abs_sum m hm] at hle
  simpa only [mul_comm g] using hsum.trans hle

 theorem nonzero_mass (m : I → ℝ) (hm : ∑ i, m i=Fintype.card I) :
    (∑ i ∈ nonzero m, m i)=((nonzero m).card:ℝ) := by
  have hp : ∀ i, (if m i ≠ 1 then m i else 0)-(if m i ≠ 1 then (1:ℝ) else 0)=m i-1 := by
    intro i
    split_ifs with hi
    · rfl
    · push Not at hi
      rw [hi]
      ring
  have hs := congrArg (fun f : I → ℝ => ∑ i, f i) (funext hp)
  simp only [sum_sub_distrib,hm,sum_const,card_univ,nsmul_eq_mul,mul_one,sub_self] at hs
  have hleft : (∑ i, if m i ≠ 1 then m i else 0)=∑ i ∈ nonzero m, m i := by
    rw [nonzero,sum_filter]
  have hright : (∑ i, if m i ≠ 1 then (1:ℝ) else 0)=((nonzero m).card:ℝ) := by
    rw [← sum_filter]
    simp [nonzero]
  rw [hleft,hright] at hs
  linarith only [hs]

 theorem grid_imbalance (Δ n : ℕ) {g : ℝ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hn : g*(n:ℝ) ≠ 1) : g ≤ |1-g*(n:ℝ)| := by
  have hne : n ≠ Δ := by intro he; exact hn (he ▸ hunit)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hc : (n:ℝ)+1 ≤ Δ := by exact_mod_cast (Nat.succ_le_of_lt hlt)
    have hs := mul_le_mul_of_nonneg_left hc hg.le
    apply le_trans _ (le_abs_self _)
    nlinarith only [hs,hunit]
  · have hc : (Δ:ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hgt)
    have hs := mul_le_mul_of_nonneg_left hc hg.le
    apply le_trans _ (neg_le_abs _)
    nlinarith only [hs,hunit]

end MetricKMedian.SourceBalance
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

omit [Fintype I] [Fintype E] in
 theorem countErase_subset (D : Actions I E) (Δ : ℕ) (e : E) : countErase D Δ e ⊆ D.erase e := by
  unfold countErase
  split_ifs
  · exact empty_subset _
  · exact Subset.rfl

omit [Fintype I] [Fintype E] in
 theorem countOpening_nonneg (D : Actions I E) (Δ : ℕ) (e : E) : 0 ≤ countOpening D Δ e := by
  unfold countOpening
  split_ifs <;> norm_num

omit [Fintype I] in
 theorem masked_degree (D : Actions I E) (Δ : ℕ)
    (hin : ∀ i, (FiniteGraph.incoming D.erase i).card ≤ Δ) (i : I) :
    (FiniteGraph.incoming (countErase D Δ) i).card ≤ Δ := by
  apply (card_le_card _).trans (hin i)
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,countErase_subset D Δ e (mem_filter.mp he).2⟩

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
namespace MetricKMedian.SourceBalance
open Finset
variable {I : Type*} [Fintype I]

omit [Fintype I] in
 theorem bias_upper (m : I → ℝ) {p φ : ℝ} (hp : 0 ≤ p) (hφ : 0 ≤ φ) (i : I) :
    bias m p φ i ≤ (1+φ)*p := by
  unfold bias
  split_ifs <;> nlinarith only [mul_nonneg hp hφ]

end MetricKMedian.SourceBalance

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential SourceBalance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem graph_mass_sum (G : I → Finset I) {Δ : ℕ} {g : ℝ}
    (hG : ∀ i, (G i).card=Δ) (hunit : g*(Δ:ℝ)=1) :
    (∑ h, mass g ((graphActions G).erase h))=(Fintype.card I:ℝ) := by
  have hc : ∀ h, mass g ((graphActions G).erase h)=∑ i, if h ∈ G i then g else 0 := by
    intro h
    rw [← sum_filter]
    simp only [mass, graphActions, sum_const, nsmul_eq_mul]
    exact mul_comm _ _
  simp_rw [hc]
  rw [sum_comm]
  have hi : ∀ i, (∑ h, if h ∈ G i then g else 0)=(1:ℝ) := by
    intro i
    rw [← sum_filter]
    simp only [filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul,hG]
    linarith only [hunit]
  simp_rw [hi]
  simp

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountInstantiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseFixedCount
open Finset PhysicalPotential SourceBalance CountGeometry CountStatistic FixedBatch
variable {I : Type} [Fintype I] [DecidableEq I]

theorem actual_count_tail_s35_oai (G : I → Finset I) {Δ n : ℕ} {g : ℚ} {p φ b : ℝ}
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < p) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hsmall : 8*p*(Δ:ℝ) ≤ φ*(g:ℝ))
    (hlarge : 1 < b*amount (fun h => mass (g:ℝ) ((graphActions G).erase h))) :
    let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
      (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
    (∀ e, (q e:ℝ)=bias m p φ (heavyParent (graphActions G) H e)) →
    (SparseEnumeratedBernoulli.law enum q hq).real.prob (fun ω => 0 < statistic
      (fun e => countOpening D Δ e-mass (g:ℝ) (countErase D Δ e))
      (fun e f => (g:ℝ)*(overlap (countErase D Δ) e f:ℝ)) ω) ≤
      96*(Δ:ℝ)^2*b/(p*φ^2*(g:ℝ)) := by
  dsimp only
  intro enum q hq hqcast
  let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
  let H := univ.filter (fun h => max 1 (b*amount m) < m h)
  have hd : 1 ≤ Δ := by
    by_contra hn
    have hz : Δ=0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero] at hunit
    linarith
  have hd' : (1:ℝ) ≤ Δ := by exact_mod_cast hd
  have hH : ∀ h ∈ H, 1 < m h := fun h hh =>
    (le_max_left _ _).trans_lt (mem_filter.mp hh).2
  have hB : ∀ h, h ∉ H → m h ≤ b*amount m := by
    intro h hh
    have hn : ¬ max 1 (b*amount m) < m h := fun ht => hh (mem_filter.mpr ⟨mem_univ _,ht⟩)
    exact (le_of_not_gt hn).trans_eq (max_eq_right (show 1 ≤ b*amount m from hlarge.le))
  have hm := graph_mass_sum G hG hunit
  have hmass : (∑ e, mass g (countErase (heavyActions (graphActions G) H) Δ e)) ≤
      2*amount m/g := by
    rw [masked_mass_sum_s35 G H Δ hg hunit hH,nonzero_mass m hm]
    apply (le_div_iff₀ hg).mpr
    simpa only [mul_comm (g:ℝ)] using nonzero_card m hm (fun h hh => grid_imbalance Δ _ hg hunit hh)
  let D := heavyActions (graphActions G) H
  let ar : HeavyAction (graphActions G) H → ℚ :=
    fun e => if e ∈ D.ordinary ∧ e ∉ balancedActions D Δ then 1 else 0
  let mr : HeavyAction (graphActions G) H → ℚ := fun e => g*(countErase D Δ e).card
  let cr : HeavyAction (graphActions G) H → HeavyAction (graphActions G) H → ℚ :=
    fun e f => g*(overlap (countErase D Δ) e f:ℚ)
  have har : ∀ e, (ar e:ℝ)=countOpening D Δ e := by
    intro e
    simp only [ar,countOpening]
    split_ifs <;> norm_num
  have hmr : ∀ e, (mr e:ℝ)=mass (g:ℝ) (countErase D Δ e) := by
    intro e
    simp only [mr,Rat.cast_mul,Rat.cast_natCast,mass]
  have hcr : ∀ e f, (cr e f:ℝ)=(g:ℝ)*(overlap (countErase D Δ) e f:ℝ) := by
    intro e f
    simp only [cr,Rat.cast_mul,Rat.cast_natCast]
  have h := SparseEnumeratedBernoulli.conditional_count_tail_s35 enum q ar mr cr hq hd' hp hφ hg hb hlarge
  simp only [har,hmr,hcr] at h
  apply h
  · intro e
    rw [hqcast]
    exact (bias_upper m hp.le hφ.le _).trans (mul_le_mul_of_nonneg_right (by linarith only [hφ1]) hp.le)
  · intro e
    exact_mod_cast (show (0:ℝ) ≤ ar e by rw [har]; exact countOpening_nonneg _ _ _)
  · intro e
    exact_mod_cast (show (0:ℝ) ≤ mr e by rw [hmr]; exact mass_nonneg hg.le _)
  · exact count_action_size_s35 G H hg.le (hg1.trans hlarge.le) hB
  · intro e f; simp only [cr,overlap_symm]
  · intro e; simp only [cr,overlap_self,Nat.cast_zero,mul_zero]
  · intro e f
    dsimp only [cr]
    exact mul_nonneg (by exact_mod_cast hg.le) (Nat.cast_nonneg _)
  · intro e
    apply scaled_overlap_row_bound _ hg.le hd
    intro i
    exact masked_degree _ Δ (fun i => le_of_eq ((heavy_incoming_card G H i).trans (hG i))) i
  · exact hmass
  · exact masked_total_bound_s35 G H hg hunit hG hH
  · exact hsmall
  · simp only [hqcast]
    exact masked_biased_linear_bound_s35 G H hg hunit hG hp.le hφ.le hH

end MetricKMedian.SparseFixedCount
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35_oai := @OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35_oai
