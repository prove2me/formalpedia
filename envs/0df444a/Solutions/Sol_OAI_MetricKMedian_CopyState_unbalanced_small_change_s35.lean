-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.unbalanced_small_change_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:59:44.235131+00:00
-- url     : https://prove2.me/submissions/a289592f-f105-4655-9244-c8d3204c3c22

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K021

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

theorem mass_sdiff [DecidableEq I] (g : ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    mass g (S \ T) = mass g S - mass g T := by
  unfold mass
  rw [Finset.card_sdiff_of_subset hTS, Nat.cast_sub (Finset.card_le_card hTS)]
  ring

end MetricKMedian.PhysicalPotential
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
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F]
variable (Δ : ℕ)

 theorem slots_disjoint {f h : F} (hfh : f ≠ h) : Disjoint (slots Δ f) (slots Δ h) := by
  apply disjoint_left.mpr
  intro i hi hj
  exact hfh (((mem_slots Δ f i).mp hi).symm.trans ((mem_slots Δ h i).mp hj))

 theorem card_resets (O : Finset F) : (resets Δ O).card=O.card*Δ := by
  rw [resets, card_biUnion (fun _ _ _ _ hne => slots_disjoint Δ hne)]
  simp

variable [Fintype F]

omit [Fintype F] in
 theorem reset_mass (O : Finset F) {g : ℝ} (hunit : g*(Δ:ℝ)=1) :
    mass g (resets Δ O)=(O.card:ℝ) := by
  rw [mass, card_resets, Nat.cast_mul]
  nlinarith only [hunit]

omit [Fintype F] in

theorem next_mass_le (A erased : Finset (Copy (F := F) Δ)) (O : Finset F)
    {g : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (he : erased ⊆ A) :
    mass g (next Δ A erased O) ≤ mass g A-mass g erased+O.card := by
  have hc := card_union_le (A \ erased) (resets Δ O)
  have hr : ((next Δ A erased O).card:ℝ) ≤ ((A \ erased).card:ℝ)+(resets Δ O).card := by
    exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hr hg
  change mass g (next Δ A erased O) ≤ _ at hm
  rw [mul_add, ← mass, ← mass, mass_sdiff g he, reset_mass Δ O hunit] at hm
  exact hm

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

variable {Δ}

omit [Fintype F] in
 theorem roundErased_subset (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : roundErased A G H Z ⊆ A := by
  rintro i hi
  obtain ⟨h,_,rfl⟩ := mem_image.mp hi
  exact h.property

end MetricKMedian.CopyState
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
 theorem countOpening_nonneg (D : Actions I E) (Δ : ℕ) (e : E) : 0 ≤ countOpening D Δ e := by
  unfold countOpening
  split_ifs <;> norm_num

omit [Fintype I] in
 theorem masked_openings (D : Actions I E) (Δ : ℕ) (ω : E → Bool) :
    (∑ e, countOpening D Δ e*CountStatistic.bit ω e)=
    (((PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω) ∩ D.ordinary).card:ℝ) := by
  have heq : (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω ∩ D.ordinary) =
      univ.filter (fun e => ω e=true ∧ e ∉ balancedActions D Δ ∧ e ∈ D.ordinary) := by
    ext e
    simp [PhysicalBatchLaw.unbalanced, and_assoc]
  rw [heq, ← sum_boole]
  apply sum_congr rfl
  intro e _
  simp only [countOpening,CountStatistic.bit]
  split_ifs <;> simp_all

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

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalCountGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.CopyState
open Finset FixedBatch PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

theorem round_count_change (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
    mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤
      (H.card:ℝ)+((Z ∩ (heavyActions (graphActions G) H).ordinary).card:ℝ)-
        mass g (Z.biUnion (heavyActions (graphActions G) H).erase) := by
  have hn := next_mass_le Δ A (roundErased A G H Z) (roundOpened A G H Z) hg hunit (roundErased_subset A G H Z)
  have he : mass g (roundErased A G H Z)=mass g (Z.biUnion (heavyActions (graphActions G) H).erase) := by
    rw [roundErased,mass,mass,card_image_of_injective _ Subtype.val_injective]
  have ho : (roundOpened A G H Z).card ≤ H.card+(Z ∩ (heavyActions (graphActions G) H).ordinary).card :=
    (card_image_le).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))
  have hor : ((roundOpened A G H Z).card:ℝ) ≤ (H.card:ℝ)+((Z ∩ (heavyActions (graphActions G) H).ordinary).card:ℝ) :=
    by exact_mod_cast ho
  rw [he] at hn
  linarith only [hn,hor]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

theorem unbalanced_small_change_s35_oai (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    {g b : ℝ} (hg : 0 < g) (hb : 0 < b) (hunit : g*(Δ:ℝ)=1)
    (hG : ∀ i, (G i).card=Δ)
    (hsmall : b*amount (fun h => mass g ((graphActions G).erase h)) ≤ 1) :
    let m := fun h => mass g ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    ∀ ω : HeavyAction (graphActions G) H → Bool,
      let D := heavyActions (graphActions G) H
      let Z := PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω
      mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤ 4/(g*b) := by
  dsimp only
  let m := fun h => mass g ((graphActions G).erase h)
  let H := univ.filter (fun h => max 1 (b*amount m) < m h)
  intro ω
  have hm := graph_mass_sum G hG hunit
  have hH := heavy_card m hg hb (fun h => mass_nonneg hg.le _) hm
    (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hn := nonzero_card m hm (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hnb : ((nonzero m).card:ℝ) ≤ 2/(g*b) := by
    apply (le_div_iff₀ (mul_pos hg hb)).mpr
    have hh := mul_le_mul_of_nonneg_right hn hb.le
    nlinarith only [hh,hsmall]
  let D := heavyActions (graphActions G) H
  let Z := PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω
  have ho : ((Z ∩ D.ordinary).card:ℝ) ≤ ((nonzero m).card:ℝ) := by
    rw [← masked_openings D Δ ω]
    apply le_trans _ (masked_opening_sum_le G H Δ hg hunit)
    apply sum_le_sum
    intro e _
    have ha := countOpening_nonneg D Δ e
    change countOpening D Δ e * bit ω e ≤ countOpening D Δ e
    unfold bit
    split_ifs
    · simp only [mul_one,le_refl]
    · simpa only [mul_zero] using ha
  have hc := round_count_change A G H Z hg.le hunit
  have he := mass_nonneg hg.le (Z.biUnion D.erase)
  calc
    _ ≤ (H.card:ℝ)+((Z ∩ D.ordinary).card:ℝ) := by linarith only [hc,he]
    _ ≤ 2/(g*b)+2/(g*b) := add_le_add hH (ho.trans hnb)
    _ = 4/(g*b) := by ring

end MetricKMedian.CopyState
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.CopyState.unbalanced_small_change_s35_oai.{u_1} := @OAI.MetricKMedian.CopyState.unbalanced_small_change_s35_oai.{u_1}
