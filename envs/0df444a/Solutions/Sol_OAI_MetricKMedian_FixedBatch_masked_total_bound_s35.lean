-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.masked_total_bound_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:03:50.996935+00:00
-- url     : https://prove2.me/submissions/68fd1094-2c43-484c-a629-742e299dc919

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K021
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_masked_mass_sum_s35

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

 theorem masked_opening_fiber (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (h : I) :
    (∑ e ∈ univ.filter (fun e => heavyParent (graphActions G) H e=h),
      countOpening (heavyActions (graphActions G) H) Δ e)=
    if h ∉ H ∧ mass g ((graphActions G).erase h) ≠ 1 then 1 else 0 := by
  by_cases hh : h ∈ H
  · rw [ite_eq_right (fun he => he.1 hh)]
    apply sum_eq_zero
    intro e he
    have heh : heavyParent (graphActions G) H e ∈ H := (mem_filter.mp he).2 ▸ hh
    have ho : e ∉ (heavyActions (graphActions G) H).ordinary := by
      rw [ordinary_heavyActions]
      exact (heavyParent_membership _ _ _).mp heh
    exact ite_eq_right (fun he => ho he.1)
  · rw [heavy_nonheavy_fiber (graphActions G) H hh,sum_singleton]
    simp only [countOpening, ordinary_heavyActions, heavy_inl_balanced (graphActions G) H Δ hh,
      Sum.isLeft_inl, true_and, hh, not_false_eq_true, mass, ne_eq,
      mass_eq_one_iff hg hunit]

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

 theorem masked_opening_sum_le (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) :
    (∑ e, countOpening (heavyActions (graphActions G) H) Δ e) ≤
      ((nonzero (fun h => mass g ((graphActions G).erase h))).card:ℝ) := by
  rw [← sum_fiberwise univ (heavyParent (graphActions G) H)]
  simp_rw [masked_opening_fiber G H Δ hg hunit]
  rw [nonzero, ← sum_boole]
  apply sum_le_sum
  intro h _
  split_ifs <;> norm_num at *
  tauto

 theorem masked_total_bound_s35_oai (G : I → Finset I) (H : Finset I) {Δ : ℕ} {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) :
    (∑ e, (countOpening (heavyActions (graphActions G) H) Δ e+
      mass g (countErase (heavyActions (graphActions G) H) Δ e))) ≤
        4*amount (fun h => mass g ((graphActions G).erase h))/g := by
  let m := fun h => mass g ((graphActions G).erase h)
  have hm := graph_mass_sum G hG hunit
  have hn := nonzero_card m hm (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hs := masked_mass_sum_s35 G H Δ hg hunit hH
  rw [nonzero_mass m hm] at hs
  have ha := masked_opening_sum_le G H Δ hg hunit
  rw [sum_add_distrib, hs]
  apply (le_div_iff₀ hg).mpr
  have ha' := mul_le_mul_of_nonneg_right ha hg.le
  dsimp only [m] at hn hs
  nlinarith only [ha',hn]

end MetricKMedian.FixedBatch
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.FixedBatch.masked_total_bound_s35_oai.{u_1} := @OAI.MetricKMedian.FixedBatch.masked_total_bound_s35_oai.{u_1}
