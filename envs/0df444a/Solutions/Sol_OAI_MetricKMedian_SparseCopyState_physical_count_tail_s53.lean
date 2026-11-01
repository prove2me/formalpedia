-- Prove2me | solution 1 for OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:35:03.681904+00:00
-- url     : https://prove2.me/submissions/f7f17853-a9c2-468a-9b3d-3fc557a7f845

import Mathlib
import Definitions.Def_OAIQ053K012
import Definitions.Def_OAIQ053K047
import Theorems.Thm_OAI_MetricKMedian_CopyState_balanced_count_change_s53
import Theorems.Thm_OAI_MetricKMedian_CopyState_unbalanced_count_change_s53
import Theorems.Thm_OAI_MetricKMedian_CopyState_unbalanced_small_change_s53
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_prob_eq_s53
import Theorems.Thm_OAI_MetricKMedian_SparseFixedCount_actual_count_tail_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem prob_congr (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω ↔ F ω) : μ.prob E = μ.prob F := by
  exact le_antisymm (μ.prob_mono fun ω => (hEF ω).mp) (μ.prob_mono fun ω => (hEF ω).mpr)

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_SourceBalance
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

 theorem amount_nonneg (m : I → ℝ) : 0 ≤ amount m := sum_nonneg (fun _ _ => le_max_right _ _)

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

theorem heavy_card (m : I → ℝ) {g b : ℝ} (hg : 0 < g) (hb : 0 < b)
    (hm0 : ∀ i, 0 ≤ m i) (hm : ∑ i, m i=Fintype.card I)
    (hgrid : ∀ i, m i ≠ 1 → g ≤ |1-m i|) :
    ((univ.filter (fun i => max 1 (b*amount m) < m i)).card:ℝ) ≤ 2/(g*b) := by
  let H := univ.filter (fun i => max 1 (b*amount m) < m i)
  have hsubset : H ⊆ nonzero m := by
    intro i hi
    have hh := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _,ne_of_gt ((le_max_left _ _).trans_lt hh)⟩
  have hhm : ((H.card:ℝ)*max 1 (b*amount m)) ≤ ∑ i ∈ H, m i := by
    have hh := sum_le_sum (s := H) (f := fun _ => max 1 (b*amount m))
      (fun i hi => (mem_filter.mp hi).2.le)
    simpa only [sum_const,nsmul_eq_mul] using hh
  have hmb := sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => hm0 i)
  rw [nonzero_mass m hm] at hmb
  have hcard := nonzero_card m hm hgrid
  have hmul := mul_le_mul_of_nonneg_left (hhm.trans hmb) hg.le
  by_cases ha : 0 < amount m
  · have hbA := mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) (b*amount m))
      (show 0 ≤ g*(H.card:ℝ) by positivity)
    have hfin : g*(H.card:ℝ)*b ≤ 2 := by
      apply (mul_le_mul_iff_left₀ ha).mp
      nlinarith only [hmul,hcard,hbA]
    apply (le_div_iff₀ (mul_pos hg hb)).mpr
    nlinarith only [hfin]
  · have ha0 : amount m=0 := le_antisymm (le_of_not_gt ha) (amount_nonneg m)
    have hn : (nonzero m).card=0 := by
      rw [ha0,mul_zero] at hcard
      have hle : ((nonzero m).card:ℝ) ≤ 0 := by nlinarith only [hcard,hg]
      exact_mod_cast le_antisymm hle (Nat.cast_nonneg _)
    have hH : H.card=0 := Nat.le_zero.mp ((card_le_card hsubset).trans_eq hn)
    change (H.card:ℝ) ≤ _
    rw [hH,Nat.cast_zero]
    positivity

end MetricKMedian.SourceBalance
end
end

end OAI
end

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

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw

theorem prob_false {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    μ.prob (fun _ => False)=0 := by
  simp only [prob, ite_false, expect_const]

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountSource
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

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePhysicalCount
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.CopyState.mem_localSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCopyState
open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic CopyState
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem physical_count_tail_s53_oai (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    {g p : ℚ} {φ b : ℝ} (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hG : ∀ i, (G i).card=Δ) (hpp : 0 ≤ p ∧ p ≤ 1)
    (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ φ*(g:ℝ)) :
    let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
      (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
    (∀ e, (q e:ℝ)=bias m (p:ℝ) φ (heavyParent (graphActions G) H e)) →
    (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ) p q hpp hq).real.prob
      (fun Z => mass (g:ℝ) A+4/((g:ℝ)*b) < mass (g:ℝ) (next Δ A (roundErased A G H Z) (roundOpened A G H Z))) ≤
        96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ)) := by
  classical
  dsimp only
  intro enum q hq hqcast
  let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
  let H := univ.filter (fun h => max 1 (b*amount m) < m h)
  let D := heavyActions (graphActions G) H
  let bad := fun Z => mass (g:ℝ) A+4/((g:ℝ)*b) <
    mass (g:ℝ) (next Δ A (roundErased A G H Z) (roundOpened A G H Z))
  have hm := graph_mass_sum G hG hunit
  have hH : (H.card:ℝ) ≤ 2/((g:ℝ)*b) := heavy_card m hg hb (fun h => mass_nonneg hg.le _) hm
    (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hc : 2/((g:ℝ)*b) ≤ 4/((g:ℝ)*b) := div_le_div_of_nonneg_right (by norm_num) (mul_pos hg hb).le
  have hbalance : (SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hpp)).real.prob
      (fun ω => bad (PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω))=0 := by
    have he : (fun ω => bad (PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω))=
        (fun _ => False) := by
      funext ω
      apply propext
      constructor
      · intro hh
        have hbnd := balanced_count_change_s53 A G H ω hg.le hunit
        dsimp only [bad] at hh
        linarith only [hbnd,hH,hc,hh]
      · exact False.elim
    have hz := (SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hpp)).real.prob_congr
      (F := fun _ => False) (fun ω => (congrFun he ω).to_iff)
    exact hz.trans (FiniteLaw.prob_false _)
  have hunbalanced : (SparseEnumeratedBernoulli.law enum q hq).real.prob
      (fun ω => bad (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω)) ≤
        96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ)) := by
    by_cases hlarge : 1 < b*amount m
    · apply le_trans _ (SparseFixedCount.actual_count_tail_s53 G hg hg1 hp hφ hφ1 hb hunit hG hsmall hlarge enum q hq hqcast)
      apply FiniteLaw.prob_mono
      intro ω hh
      have hbnd := unbalanced_count_change_s53 A G H ω hg.le hunit
      dsimp only [bad] at hh
      linarith only [hh,hbnd,hH,hc]
    · have he : (fun ω => bad (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω))=(fun _ => False) := by
        funext ω
        apply propext
        constructor
        · intro hh
          have hbnd := unbalanced_small_change_s53 A G hg hb hunit hG (le_of_not_gt hlarge) ω
          dsimp only [bad] at hh
          linarith only [hh,hbnd]
        · exact False.elim
      have hz := (SparseEnumeratedBernoulli.law enum q hq).real.prob_congr
        (F := fun _ => False) (fun ω => (congrFun he ω).to_iff)
      rw [hz,FiniteLaw.prob_false]
      positivity
  rw [SparseEnumeratedBatch.prob_eq_s53]
  change (1/2)*(SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hpp)).real.prob (fun ω => bad (PhysicalBatchLaw.balanced _ _ ω))+
    (1/2)*(SparseEnumeratedBernoulli.law enum q hq).real.prob (fun ω => bad (PhysicalBatchLaw.unbalanced _ ω)) ≤ _
  rw [hbalance, mul_zero, zero_add]
  have hnonneg : 0 ≤ 96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ)) := by positivity
  linarith only [hunbalanced,hnonneg]

end MetricKMedian.SparseCopyState
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53_oai := @OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53_oai
