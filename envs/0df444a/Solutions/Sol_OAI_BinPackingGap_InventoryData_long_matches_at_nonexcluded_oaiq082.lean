-- Prove2me | solution 1 for OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded_oaiq082
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:05:54.776835+00:00
-- url     : https://prove2.me/submissions/71ddac76-b655-4e15-9b58-b6aebe219731

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C021
import Theorems.Thm_OAI_BinPackingGap_InventoryData_badAnchorsAt_card_le_oaiq082

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_FractionWidth
attribute [-instance] _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

theorem chosen_injective (p : Packing I b) {J : Type*}
    (bin : J → Fin b) (hbin : Function.Injective bin)
    (chosen : J → I.Item) (hchosen : ∀ j, chosen j ∈ p.binItems (bin j)) :
    Function.Injective chosen := by
  intro j k hjk
  apply hbin
  have hj := (p.mem_binItems (bin j) (chosen j)).mp (hchosen j)
  have hk := (p.mem_binItems (bin k) (chosen k)).mp (hchosen k)
  rw [hjk] at hj
  exact hj.symm.trans hk

end Packing

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalar
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.InventoryData.roleCopiesFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

theorem itemAtRole_mem (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    p.itemAtRole subclass t r ∈ p.binItems t.val :=
  (p.tableEquiv subclass t r).property

theorem itemAtRole_injective (p : Packing I b) (subclass : I.Item → Subclass)
    (r : Role) : Function.Injective (fun t => p.itemAtRole subclass t r) :=
  p.chosen_injective Subtype.val Subtype.val_injective
    (fun t => p.itemAtRole subclass t r) (fun t => p.itemAtRole_mem subclass t r)

end Packing

end

open scoped BigOperators

theorem encodedSize_sum {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ) :
    (∑ i, encodedSize (s i) (label i) (w i)) =
      1 + gamma * (primaryTotal s : ℚ) +
        mu n * (secondaryTotal s label : ℚ) + nu n * coordinateTotal w := by
  simp [encodedSize, primaryTotal, secondaryTotal, coordinateTotal,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem feasible_iff_coordinateSum_nonpos {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hp : primaryTotal s = 0) (hq : secondaryTotal s label = 0) :
    ((∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) ↔ coordinateTotal w ≤ 0 := by
  rw [encodedSize_sum, hp, hq]
  norm_num only [Int.cast_zero, mul_zero, add_zero]
  constructor
  · intro h
    have hmul : nu n * coordinateTotal w ≤ nu n * 0 := by linarith
    exact le_of_mul_le_mul_left hmul (nu_pos n)
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h (nu_pos n).le
    linarith

namespace Packing

variable {I : Instance} {b n : ℕ}

theorem sum_fiveEquiv (p : Packing I b) (j : Fin b) (hc : (p.binItems j).card = 5)
    {M : Type*} [AddCommMonoid M] (f : I.Item → M) :
    (∑ i : Fin 5, f (p.fiveEquiv j hc i).val) = ∑ i ∈ p.binItems j, f i := by
  rw [(p.fiveEquiv j hc).sum_comp (fun i : p.binItems j => f i.val)]
  change (∑ i ∈ (p.binItems j).attach, f i.val) = ∑ i ∈ p.binItems j, f i
  exact Finset.sum_attach (p.binItems j) f

theorem sum_itemAtRole (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) {M : Type*} [AddCommMonoid M] (f : I.Item → M) :
    (∑ r : Role, f (p.itemAtRole subclass t r)) = ∑ i ∈ p.binItems t.val, f i := by
  change (∑ r : Role, f (p.tableEquiv subclass t r).val) =
    ∑ i ∈ p.binItems t.val, f i
  rw [(p.tableEquiv subclass t).sum_comp (fun i : p.binItems t.val => f i.val)]
  change (∑ i ∈ (p.binItems t.val).attach, f i.val) = ∑ i ∈ p.binItems t.val, f i
  exact Finset.sum_attach (p.binItems t.val) f

theorem table_secondary_eq (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (t : p.TableBin subclass) (x d a : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel x d a r) :
    (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) =
      labelSecondary x d a := by
  rw [← p.sum_itemAtRole subclass t]
  simp only [secondaryScore, p.itemAtRole_role, hl]
  rw [Role.sum_univ]
  simp [tableRoleLabel, labelSecondary]
  ring

theorem table_coordinate_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (t : p.TableBin subclass)
    (hq : (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) = 0) :
    (∑ i ∈ p.binItems t.val, coordinate i) ≤ 0 := by
  let e := p.fiveEquiv t.val t.property.1
  have hp : BinPackingGap.primaryTotal (fun i => subclass (e i).val) = 0 := by
    change (∑ i : Fin 5,
      primaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1 (fun i => primaryScore (subclass i))]
    exact t.property.2
  have hq' : secondaryTotal (fun i => subclass (e i).val)
      (fun i => label (e i).val) = 0 := by
    change (∑ i : Fin 5,
      secondaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)
        (label (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1
      (fun i => secondaryScore (subclass i) (label i))]
    exact hq
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity t.val
  have hw := (feasible_iff_coordinateSum_nonpos
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) hp hq').mp hcap
  change (∑ i : Fin 5, coordinate (p.fiveEquiv t.val t.property.1 i).val) ≤ 0 at hw
  rw [p.sum_fiveEquiv t.val t.property.1 coordinate] at hw
  exact hw

theorem table_coordinate_nonpos_of_same_label (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (t : p.TableBin subclass) (v : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel v v v r) :
    (∑ r : Role, coordinate (p.itemAtRole subclass t r)) ≤ 0 := by
  rw [p.sum_itemAtRole]
  apply p.table_coordinate_nonpos subclass label coordinate hsize t
  rw [p.table_secondary_eq subclass label t v v v hl]
  simp [labelSecondary]
  ring

end Packing

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_CompletionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

theorem lambda_lt_tenth (m R D ell : ℕ) : lambda m R D ell < 1 / 10 := by
  have h := (lambda_le_gap m R D ell).trans (gap_le_one_sixteen m R)
  linarith

end BinPackingGap.Geometry

namespace BinPackingGap

theorem completion_le_baseline (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ)
    (hglobal : 0 ≤ globalLen) (hlocal : 0 ≤ localLen) (hdelta : 0 ≤ delta) :
    completion b short globalLen localLen delta ≤ b := by
  cases short <;> simp only [completion_false, completion_true] <;> linarith

theorem completionInterval_short_zero_lengths (b delta : ℚ) :
    completionInterval b true 0 0 delta = Set.Ico (b - delta) b := by
  simp [completionInterval]

theorem completion_minus_gt_one (b : ℚ) (short : Bool) (globalLen localLen delta lambdaOne : ℚ)
    (hbaseline : 4 ≤ b) (hshort : short = false) (hglobal : globalLen ≤ 1)
    (hlocal : localLen ≤ lambdaOne) (hlambda : lambdaOne < 1) :
    1 < completion b short globalLen localLen delta := by
  subst short
  rw [completion_false]
  linarith

theorem completion_minus_geometry_gt_one (m R D L : ℕ) (b : ℚ) (short : Bool)
    (globalLen localLen : ℚ) (hbaseline : 4 ≤ b) (hshort : short = false)
    (hglobal : globalLen ≤ 1) (hlocal : localLen ≤ Geometry.lambda m R D 1) :
    1 < completion b short globalLen localLen (Geometry.delta m R D L) := by
  apply completion_minus_gt_one b short globalLen localLen _ (Geometry.lambda m R D 1)
    hbaseline hshort hglobal hlocal
  linarith [Geometry.lambda_lt_tenth m R D 1]

theorem completion_job_interval (m R D L : ℕ) (r : Geometry.Position m R) :
    completionInterval (Geometry.baseline m R r) true 0 0 (Geometry.delta m R D L) =
      Set.Ico (Geometry.baseline m R r - Geometry.delta m R D L)
        (Geometry.baseline m R r) :=
  completionInterval_short_zero_lengths _ _

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_CurrentMatches
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.InventoryData.roleCopiesFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace CoverageCounts

section FiniteCounts

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
theorem ordered_short_long_partition [LinearOrder γ]
    (s : Finset α) (position : α → γ) (current : γ) (short : α → Prop)
    [DecidablePred short] (horder : ∀ i ∈ s, position i ≤ current) :
    s.card = (s.filter fun i => position i < current).card +
      (s.filter fun i => position i = current ∧ short i).card +
      (s.filter fun i => position i = current ∧ ¬ short i).card := by
  classical
  have hexact : (s.filter fun i => ¬ position i < current) =
      (s.filter fun i => position i = current) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨his, hi⟩
      exact ⟨his, le_antisymm (horder i his) (le_of_not_gt hi)⟩
    · rintro ⟨his, hi⟩
      exact ⟨his, by rw [hi]; exact lt_irrefl _⟩
  have hpositions := Finset.card_filter_add_card_filter_not
    (s := s) (fun i => position i < current)
  rw [hexact] at hpositions
  have hlengths := Finset.card_filter_add_card_filter_not
    (s := s.filter fun i => position i = current) short
  simp only [Finset.filter_filter] at hlengths
  omega

theorem card_le_good_card_add {s bad : Finset α} {K : ℕ}
    (hbad : bad.card ≤ K) : s.card ≤ (s \ bad).card + K := by
  have hinter : (s ∩ bad).card ≤ K :=
    (Finset.card_le_card Finset.inter_subset_right).trans hbad
  have hsplit := Finset.card_sdiff_add_card_inter s bad
  omega

omit [DecidableEq β] in
theorem card_add_card_le_of_disjoint_injections
    (s t : Finset α) (resources : Finset β) (row : α → β)
    (hdis : Disjoint s t)
    (hmap : ∀ i ∈ s ∪ t, row i ∈ resources)
    (hinj : Set.InjOn row (↑(s ∪ t : Finset α) : Set α)) : s.card + t.card ≤ resources.card := by
  rw [← Finset.card_union_of_disjoint hdis]
  exact Finset.card_le_card_of_injOn row hmap hinj

omit [DecidableEq β] in
theorem card_three_le_of_disjoint_injections
    (s t u : Finset α) (resources : Finset β) (row : α → β)
    (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u)
    (hmap : ∀ i ∈ (s ∪ t) ∪ u, row i ∈ resources)
    (hinj : Set.InjOn row (↑((s ∪ t) ∪ u : Finset α) : Set α)) :
    s.card + t.card + u.card ≤ resources.card := by
  have hdis : Disjoint (s ∪ t) u := by
    apply Finset.disjoint_left.mpr
    intro i hi hu
    rcases Finset.mem_union.mp hi with hs | ht
    · exact Finset.disjoint_left.mp hsu hs hu
    · exact Finset.disjoint_left.mp htu ht hu
  have hcount := card_add_card_le_of_disjoint_injections
    (s ∪ t) u resources row hdis hmap hinj
  rwa [Finset.card_union_of_disjoint hst] at hcount

end FiniteCounts

theorem displaced_baseline_bound {A B tree jobs used goodEarlier ξ K : ℕ}
    (hA : A ≤ tree + used) (hB : B = tree + jobs)
    (hrows : used + goodEarlier + ξ ≤ 2 * jobs)
    (hkeys : jobs ≤ goodEarlier + 3 * K) : A + ξ ≤ B + 3 * K := by
  omega

theorem displaced_short_correction {A B C I d K ξ xplus shortM : ℕ}
    (hpartition : C = A + I) (hdeadline : B + d ≤ C + 3 * K)
    (hbaseline : A + ξ ≤ B + 3 * K) (hcoverage : I ≤ xplus + shortM) :
    d + ξ ≤ xplus + shortM + 6 * K := by
  omega

theorem short_le_displaced_add_long {d K ξ goodCurrent shortM shortG longG : ℕ}
    (hkeys : d ≤ goodCurrent + 3 * K)
    (hpartition : goodCurrent = ξ + shortG + longG)
    (hshort : shortM + shortG ≤ d) : shortM ≤ ξ + longG + 3 * K := by
  omega

theorem long_match_lower_bound {d K ξ xplus shortM longG : ℕ}
    (hcorrection : d + ξ ≤ xplus + shortM + 6 * K)
    (hshort : shortM ≤ ξ + longG + 3 * K) :
    d ≤ longG + xplus + 9 * K := by
  omega

end CoverageCounts
end BinPackingGap

namespace BinPackingGap
namespace Coverage

variable {I : Instance} {b n : ℕ}

theorem mainTuplesAt_subset_good (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    mainTuplesAt p cls label v ⊆ goodTuplesAt p cls label v := by
  classical
  exact Finset.filter_subset _ _

theorem edgeTuplesAt_subset_good (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    edgeTuplesAt p cls label v ⊆ goodTuplesAt p cls label v := by
  classical
  exact Finset.filter_subset _ _

theorem mainTuplesAt_disjoint_edge (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v w : Fin n) :
    Disjoint (mainTuplesAt p cls label v) (edgeTuplesAt p cls label w) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  exact ((mem_mainTuplesAt p cls label v t).mp ht).2.2
    (((mem_edgeTuplesAt p cls label w t).mp hu).2.2)

@[simp] theorem roleItems_card (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) : (roleItems p cls s role).card = s.card :=
  Finset.card_image_of_injective s (p.itemAtRole_injective cls role)

theorem card_le_role_resources (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) (resources : Finset I.Item)
    (hmap : ∀ t ∈ s, p.itemAtRole cls t role ∈ resources) : s.card ≤ resources.card :=
  Finset.card_le_card_of_injOn (fun t => p.itemAtRole cls t role) hmap
    (p.itemAtRole_injective cls role).injOn

theorem card_three_le_row_resources (p : Packing I b) (cls : I.Item → Subclass)
    (s t u : Finset (p.TableBin cls)) (resources : Finset I.Item)
    (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u)
    (hmap : ∀ x ∈ (s ∪ t) ∪ u, p.itemAtRole cls x .x ∈ resources) :
    s.card + t.card + u.card ≤ resources.card :=
  CoverageCounts.card_three_le_of_disjoint_injections s t u resources
    (fun x => p.itemAtRole cls x .x) hst hsu htu hmap
    (p.itemAtRole_injective cls .x).injOn

theorem completion_prefix_decomposition (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (finish : p.TableBin cls → ℚ)
    (hle : ∀ t ∈ mainTuplesAt p cls label v, finish t ≤ baseline (p.itemAtRole cls t .x))
    (a : ℚ) :
    (completionPrefixAt p cls label v finish a).card =
      (baselinePrefixAt p cls label v baseline a).card +
        (coveringTuplesAt p cls label v baseline finish a).card :=
  CoverageCounts.interval_prefix_card (mainTuplesAt p cls label v) finish
    (fun t => baseline (p.itemAtRole cls t .x)) hle a

theorem good_deadline_subset_completed_anchor_image
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ)
    (hfeasible : ∀ t ∈ mainTuplesAt p cls label v,
      finish t ≤ deadline (p.itemAtRole cls t .anchor)) :
    deadlinePrefixAt (I := I) cls label v deadline a \ badAnchorsAt p cls label v ⊆
      roleItems p cls (completionPrefixAt p cls label v finish a) .anchor := by
  classical
  intro i hi
  obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨hcls, hlabel, hdeadline⟩ :=
    (mem_deadlinePrefixAt cls label v deadline a i).mp hi
  have hanchor : i ∈ anchorItemsAt (I := I) cls label v := by
    apply (mem_anchorItemsAt cls label v i).mpr
    exact ⟨by rw [hcls]; rfl, hlabel⟩
  have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
    by_contra h
    exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
  have hM : t ∈ mainTuplesAt p cls label v := by
    have htgood := (mem_goodTuplesAt p cls label v t).mp ht
    refine (mem_mainTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, ?_⟩
    intro hedge
    have hsub := p.itemAtRole_subclass cls t .anchor
    rw [hedge] at hsub
    have hnot : (Subclass.z : Subclass) = .y := by
      calc
        Subclass.z = cls i := hcls.symm
        _ = cls (p.itemAtRole cls t .anchor) := congrArg cls hti.symm
        _ = Subclass.y := hsub
    cases hnot
  apply Finset.mem_image.mpr
  refine ⟨t, ?_, hti⟩
  apply Finset.mem_filter.mpr
  refine ⟨hM, (hfeasible t hM).trans ?_⟩
  simpa only [hti] using hdeadline

theorem deadline_prefix_le_completion_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (hfeasible : ∀ t ∈ mainTuplesAt p cls label v,
      finish t ≤ deadline (p.itemAtRole cls t .anchor)) :
    (deadlinePrefixAt (I := I) cls label v deadline a).card ≤
      (completionPrefixAt p cls label v finish a).card + 3 * K := by
  have hcount := Finset.card_le_card
    (good_deadline_subset_completed_anchor_image p cls label v deadline finish a hfeasible)
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add
    (s := deadlinePrefixAt (I := I) cls label v deadline a) hbad
  omega

theorem baseline_prefix_row_partition
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ) :
    (baselinePrefixAt p cls label v baseline a).card =
      (mainTreePrefixAt p cls label v baseline a).card +
        (mainJobPrefixAt p cls label v baseline a).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := baselinePrefixAt p cls label v baseline a)
    (fun t => cls (p.itemAtRole cls t .x) = .s)
  simpa only [mainTreePrefixAt, mainJobPrefixAt, Nat.add_comm] using h.symm

theorem main_tree_prefix_le_inventory
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ) :
    (mainTreePrefixAt p cls label v baseline a).card ≤
      (treeRowPrefixAt (I := I) cls label v baseline a).card := by
  classical
  apply card_le_role_resources p cls _ .x _
  intro t ht
  obtain ⟨ht, hnots⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht, hbase⟩ := Finset.mem_filter.mp ht
  obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp ht
  have hrole := (role_eq_x_iff (cls (p.itemAtRole cls t .x))).mp
    (p.itemAtRole_role cls t .x)
  have htree : cls (p.itemAtRole cls t .x) = .tp ∨
      cls (p.itemAtRole cls t .x) = .tm := by
    rcases hrole with hp | hm | hs
    · exact Or.inl hp
    · exact Or.inr hm
    · exact False.elim (hnots hs)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htree, hgood.1.trans hlabel, hbase⟩

theorem good_key_subset_edge_anchor_image
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) :
    keyPrefixAt (I := I) cls label v keyBaseline a \ badAnchorsAt p cls label v ⊆
      roleItems p cls (edgePrefixAt p cls label v keyBaseline a) .anchor := by
  classical
  intro i hi
  obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨_, hcls, hlabel, hbase⟩ := Finset.mem_filter.mp hi
  have hanchor : i ∈ anchorItemsAt (I := I) cls label v :=
    (mem_anchorItemsAt cls label v i).mpr ⟨by rw [hcls]; rfl, hlabel⟩
  have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
    by_contra h
    exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
  have hpattern : p.tablePattern cls t = .edgeJob := by
    have hsub : patternSubclass (p.tablePattern cls t) .anchor = .y :=
      (p.itemAtRole_subclass cls t .anchor).symm.trans ((congrArg cls hti).trans hcls)
    cases hp : p.tablePattern cls t <;> simp_all [patternSubclass]
  have htgood := (mem_goodTuplesAt p cls label v t).mp ht
  have hG : t ∈ edgeTuplesAt p cls label v :=
    (mem_edgeTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, hpattern⟩
  apply Finset.mem_image.mpr
  refine ⟨t, Finset.mem_filter.mpr ⟨hG, ?_⟩, hti⟩
  simpa only [hti] using hbase

theorem key_prefix_le_edge_prefix_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    (keyPrefixAt (I := I) cls label v keyBaseline a).card ≤
      (edgePrefixAt p cls label v keyBaseline a).card + 3 * K := by
  have hcount := Finset.card_le_card
    (good_key_subset_edge_anchor_image p cls label v keyBaseline a)
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add
    (s := keyPrefixAt (I := I) cls label v keyBaseline a) hbad
  omega

theorem edge_row_mem_job_prefix
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ)
    {t : p.TableBin cls} (ht : t ∈ edgeTuplesAt p cls label v)
    (hbase : baseline (p.itemAtRole cls t .x) ≤ a) :
    p.itemAtRole cls t .x ∈ jobRowPrefixAt (I := I) cls label v baseline a := by
  obtain ⟨hgood, hlabel, hpattern⟩ := (mem_edgeTuplesAt p cls label v t).mp ht
  have hcls : cls (p.itemAtRole cls t .x) = .s := by
    rw [p.itemAtRole_subclass cls t .x, hpattern]
    rfl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls, hgood.1.trans hlabel, hbase⟩

theorem displaced_baseline_prefix_le
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (a : ℚ)
    (extra : Finset (p.TableBin cls)) (B jobs K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor))
    (hextra : extra ⊆ edgeTuplesAt p cls label v)
    (hextraRows : ∀ t ∈ extra, baseline (p.itemAtRole cls t .x) ≤ a)
    (hextraDis : Disjoint (edgePrefixAt p cls label v keyBaseline a) extra)
    (hjobStock : (jobRowPrefixAt (I := I) cls label v baseline a).card = 2 * jobs)
    (hkeyStock : (keyPrefixAt (I := I) cls label v keyBaseline a).card = jobs)
    (hbaselineStock : B = (treeRowPrefixAt (I := I) cls label v baseline a).card + jobs) :
    (baselinePrefixAt p cls label v baseline a).card + extra.card ≤ B + 3 * K := by
  classical
  let M := mainJobPrefixAt p cls label v baseline a
  let E := edgePrefixAt p cls label v keyBaseline a
  have hMsub : M ⊆ mainTuplesAt p cls label v := by
    intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hEsub : E ⊆ edgeTuplesAt p cls label v := Finset.filter_subset _ _
  have hME : Disjoint M E :=
    (mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hEsub
  have hMX : Disjoint M extra :=
    (mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hextra
  have hmap : ∀ t ∈ (M ∪ E) ∪ extra,
      p.itemAtRole cls t .x ∈ jobRowPrefixAt (I := I) cls label v baseline a := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hprefix, hcls⟩ := Finset.mem_filter.mp ht
        obtain ⟨htM, hbase⟩ := Finset.mem_filter.mp hprefix
        obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp htM
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcls, hgood.1.trans hlabel, hbase⟩
      · obtain ⟨htG, hbase⟩ := Finset.mem_filter.mp ht
        exact edge_row_mem_job_prefix p cls label v baseline a htG
          ((horder t htG).trans hbase)
    · exact edge_row_mem_job_prefix p cls label v baseline a (hextra ht)
        (hextraRows t ht)
  have hrows := card_three_le_row_resources p cls M E extra
    (jobRowPrefixAt (I := I) cls label v baseline a) hME hMX hextraDis hmap
  rw [hjobStock] at hrows
  have hkeys := key_prefix_le_edge_prefix_add_loss p cls label v keyBaseline a K hbad
  rw [hkeyStock] at hkeys
  have hsplit := baseline_prefix_row_partition p cls label v baseline a
  have htrees := main_tree_prefix_le_inventory p cls label v baseline a
  have hmain : (baselinePrefixAt p cls label v baseline a).card ≤
      (treeRowPrefixAt (I := I) cls label v baseline a).card + M.card := by
    dsimp only [M]
    omega
  exact CoverageCounts.displaced_baseline_bound hmain hbaselineStock hrows hkeys

theorem key_subset_le_matching_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keys : Finset I.Item) (matchedTuples : Finset (p.TableBin cls)) (K : ℕ)
    (hkeys : ∀ i ∈ keys, cls i = .y ∧ label i = some v)
    (hselect : ∀ t ∈ edgeTuplesAt p cls label v,
      p.itemAtRole cls t .anchor ∈ keys → t ∈ matchedTuples)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    keys.card ≤ matchedTuples.card + 3 * K := by
  classical
  have hsubset : keys \ badAnchorsAt p cls label v ⊆ roleItems p cls matchedTuples .anchor := by
    intro i hi
    obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hcls, hlabel⟩ := hkeys i hi
    have hanchor : i ∈ anchorItemsAt (I := I) cls label v :=
      (mem_anchorItemsAt cls label v i).mpr ⟨by rw [hcls]; rfl, hlabel⟩
    have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
      by_contra h
      exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
    have hpattern : p.tablePattern cls t = .edgeJob := by
      have hsub : patternSubclass (p.tablePattern cls t) .anchor = .y :=
        (p.itemAtRole_subclass cls t .anchor).symm.trans ((congrArg cls hti).trans hcls)
      cases hp : p.tablePattern cls t <;> simp_all [patternSubclass]
    have htgood := (mem_goodTuplesAt p cls label v t).mp ht
    have hG : t ∈ edgeTuplesAt p cls label v :=
      (mem_edgeTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, hpattern⟩
    refine Finset.mem_image.mpr ⟨t, hselect t hG ?_, hti⟩
    simpa only [hti] using hi
  have hcount := Finset.card_le_card hsubset
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add (s := keys) hbad
  omega

theorem current_key_count_le_matches_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    (currentKeyItemsAt (I := I) cls label v keyBaseline current).card ≤
      (currentEdgeTuplesAt p cls label v keyBaseline current).card + 3 * K := by
  apply key_subset_le_matching_add_loss p cls label v _ _ K _ _ hbad
  · intro i hi
    obtain ⟨_, hcls, hlabel, _⟩ := Finset.mem_filter.mp hi
    exact ⟨hcls, hlabel⟩
  · intro t ht hi
    exact Finset.mem_filter.mpr ⟨ht, (Finset.mem_filter.mp hi).2.2.2⟩

theorem current_match_partition
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor)) :
    (currentEdgeTuplesAt p cls label v keyBaseline current).card =
      (displacedTuplesAt p cls label v baseline keyBaseline current).card +
      (currentShortEdgeAt p cls label v baseline keyBaseline short current).card +
      (currentLongEdgeAt p cls label v baseline keyBaseline short current).card := by
  apply CoverageCounts.ordered_short_long_partition
    (currentEdgeTuplesAt p cls label v keyBaseline current)
    (fun t => baseline (p.itemAtRole cls t .x)) current
    (fun t => short (p.itemAtRole cls t .x) = true)
  intro t ht
  obtain ⟨ht, hcurrent⟩ := Finset.mem_filter.mp ht
  exact (horder t ht).trans_eq hcurrent

theorem current_short_consumption_le_stock
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (hshortJob : ∀ i, short i = true → cls i = .s) :
    (currentShortMainAt p cls label v baseline short current).card +
      (currentShortEdgeAt p cls label v baseline keyBaseline short current).card ≤
        (currentShortItemsAt (I := I) cls label v baseline short current).card := by
  classical
  let M := currentShortMainAt p cls label v baseline short current
  let G := currentShortEdgeAt p cls label v baseline keyBaseline short current
  have hMsub : M ⊆ mainTuplesAt p cls label v := Finset.filter_subset _ _
  have hGsub : G ⊆ edgeTuplesAt p cls label v := by
    intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  apply CoverageCounts.card_add_card_le_of_disjoint_injections M G
    (currentShortItemsAt (I := I) cls label v baseline short current)
    (fun t => p.itemAtRole cls t .x)
    ((mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hGsub)
    _ (p.itemAtRole_injective cls .x).injOn
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · obtain ⟨ht, hbase, hshort⟩ := Finset.mem_filter.mp ht
    obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshortJob _ hshort,
      hgood.1.trans hlabel, hbase, hshort⟩
  · obtain ⟨ht, hbase, hshort⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨hgood, hlabel, _⟩ := (mem_edgeTuplesAt p cls label v t).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshortJob _ hshort,
      hgood.1.trans hlabel, hbase, hshort⟩

theorem current_long_matches_from_correction
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (d K xplus : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor))
    (hshortJob : ∀ i, short i = true → cls i = .s)
    (hkeys : (currentKeyItemsAt (I := I) cls label v keyBaseline current).card = d)
    (hshortStock : (currentShortItemsAt (I := I) cls label v baseline short current).card = d)
    (hcorrection : d + (displacedTuplesAt p cls label v baseline keyBaseline current).card ≤
      xplus + (currentShortMainAt p cls label v baseline short current).card + 6 * K) :
    d ≤ (currentLongEdgeAt p cls label v baseline keyBaseline short current).card +
      xplus + 9 * K := by
  have hgood := current_key_count_le_matches_add_loss p cls label v keyBaseline current K hbad
  rw [hkeys] at hgood
  have hpartition := current_match_partition p cls label v baseline keyBaseline short current horder
  have hshort := current_short_consumption_le_stock p cls label v baseline keyBaseline
    short current hshortJob
  rw [hshortStock] at hshort
  exact CoverageCounts.long_match_lower_bound hcorrection
    (CoverageCounts.short_le_displaced_add_long hgood hpartition hshort)

end Coverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_IntegerTreeGeometry
attribute [-instance] _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.TreeGeometry

open _root_.OAI.BinPackingGap.Geometry UniformTree

theorem cell_subset_of_prefix (m R D : ℕ) (s : Side) {u v : List ℕ}
    (h : u.IsPrefix v) (hv : BoundedAddress D v) :
    cell m R D s v ⊆ cell m R D s u := by
  have hb := prefix_endpoints m R D s h hv
  intro x hx
  exact ⟨hb.1.trans hx.1, hx.2.trans hb.2⟩

theorem nodeCell_subset_of_ancestor (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) {u v : T.Node} (h : ancestor u v) :
    nodeCell m R D s v ⊆ nodeCell m R D s u :=
  cell_subset_of_prefix m R D s h (boundedAddress_node v hD)

theorem nodeCell_subset_root (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) (v : T.Node) :
    nodeCell m R D s v ⊆ Set.Icc (rootOffset s) (rootOffset s + 1) := by
  simpa [nodeCell, cell] using
    nodeCell_subset_of_ancestor m R D s hD (root_ancestor v)

end BinPackingGap.TreeGeometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

private theorem elementAtRole_mk (i : D.Item) (r : Role) (h : i.1 = r) :
    (⟨r, elementAtRole i r h⟩ : D.Item) = i := by
  rcases i with ⟨s, i⟩
  dsimp at h
  cases h
  rfl

@[simp] theorem roleCopy_item (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    e ⟨r, roleCopy p e t r⟩ = p.itemAtRole (subclass e) t r := by
  rw [roleCopy, elementAtRole_mk, e.apply_symm_apply]

theorem roleCopy_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemSubclass ⟨r, roleCopy p e t r⟩ = patternSubclass (p.tablePattern (subclass e) t) r := by
  have h := p.itemAtRole_subclass (subclass e) t r
  rw [← roleCopy_item p e t r] at h
  simpa only [subclass, Function.comp_apply, e.symm_apply_apply] using h

theorem selected_global_resource_iff (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (s : GlobalSpecies D.graph) :
    p.itemAtRole (subclass e) t .«global» ∈ globalResources e s ↔
      (globalCopy p e t).1 = s := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (mem_globalResources e s _).mp h
    rw [← roleCopy_item p e t .«global»] at hi
    have he := e.injective hi
    have hg : (⟨s, i⟩ : D.GlobalCopy) = globalCopy p e t := by
      exact @sigma_mk_injective Role D.RoleCopies .«global» _ _ he
    exact (congrArg Sigma.fst hg).symm
  · intro h
    rcases hg : globalCopy p e t with ⟨s', i⟩
    have hs : s' = s := by simpa only [hg] using h
    subst s'
    apply (mem_globalResources e s _).mpr
    refine ⟨i, ?_⟩
    rw [← roleCopy_item p e t .«global»]
    exact congrArg (fun x : D.GlobalCopy => e ⟨.«global», x⟩) hg.symm

@[simp] theorem selected_row_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .x) = some (rowCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .x)) =
    some (rowCopy p e t).1
  rw [← roleCopy_item p e t .x, e.symm_apply_apply]
  rfl

@[simp] theorem selected_anchor_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .anchor) = some (anchorCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .anchor)) =
    some (anchorCopy p e t).1
  rw [← roleCopy_item p e t .anchor, e.symm_apply_apply]
  rfl

@[simp] theorem selected_local_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .«local») = some (localCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .«local»)) =
    some (localCopy p e t).1
  rw [← roleCopy_item p e t .«local», e.symm_apply_apply]
  rfl

theorem good_row_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (rowCopy p e t).1 = v := by
  have ht' := (Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht
  have h := ht'.1.1.trans ht'.2
  rw [selected_row_label] at h
  exact Option.some.inj h

theorem good_anchor_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (anchorCopy p e t).1 = v := by
  have h := ((Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht).2
  rw [selected_anchor_label] at h
  exact Option.some.inj h

theorem good_local_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (localCopy p e t).1 = v := by
  have ht' := (Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht
  have h := ht'.1.2.trans ht'.2
  rw [selected_local_label] at h
  exact Option.some.inj h

@[simp] theorem mem_zeroPositiveTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) :
    t ∈ zeroPositiveTuples p e v ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
        D.globalUnit (globalCopy p e t) = false ∧
          p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v := by
  classical
  simp [zeroPositiveTuples, and_assoc]

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_CoordinateOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

variable {m R : ℕ}

theorem posLE_iff_not_posLT {r s : Position m R} : posLE r s ↔ ¬ posLT s r := by
  simp only [posLE, posLT, Prod.ext_iff, Fin.ext_iff]
  omega

theorem theta_jump {e f : Fin m} (hef : e < f) :
    (R : ℚ) * ((R : ℚ) + 1) ^ e.val ≤ theta R f - theta R e := by
  have hp : ((R : ℚ) + 1) ^ (e.val + 1) ≤ ((R : ℚ) + 1) ^ f.val :=
    pow_le_pow_right₀ (base_one_le R) (Nat.succ_le_of_lt hef)
  rw [pow_succ] at hp
  unfold theta
  nlinarith

theorem theta_jump_ge_heightCode {r : Position m R} {f : Fin m} (hef : r.1 < f) :
    heightCode R r + 1 ≤ theta R f - theta R r.1 :=
  (by linarith [heightCode_le_edgeMax R r] :
    heightCode R r + 1 ≤ (R : ℚ) * ((R : ℚ) + 1) ^ r.1.val).trans (theta_jump hef)

theorem baseline_lt_iff {r s : Position m R} :
    baseline m R r < baseline m R s ↔ posLT r s := by
  constructor
  · intro h
    rcases posLT_trichotomy r s with hrs | hrs | hsr
    · exact hrs
    · subst s
      exact (lt_irrefl _ h).elim
    · have hg := baseline_gap_of_posLT hsr
      have hp := gap_pos m R
      linarith
  · intro h
    have hg := baseline_gap_of_posLT h
    have hp := gap_pos m R
    linarith

theorem baseline_le_iff {r s : Position m R} :
    baseline m R r ≤ baseline m R s ↔ posLE r s := by
  rw [posLE_iff_not_posLT, ← baseline_lt_iff]
  constructor
  · intro hle hlt
    linarith
  · intro h
    by_contra h'
    apply h
    linarith

theorem baseline_eq_iff {r s : Position m R} :
    baseline m R r = baseline m R s ↔ r = s := by
  constructor
  · intro h
    rcases posLT_trichotomy r s with hrs | hrs | hsr
    · exact (ne_of_lt (baseline_lt_iff.mpr hrs) h).elim
    · exact hrs
    · exact (ne_of_lt (baseline_lt_iff.mpr hsr) h.symm).elim
  · rintro rfl
    rfl

theorem baseline_le_jobInterior_iff {Δ : ℚ} (hΔ : 0 < Δ)
    (hΔg : Δ < gap m R) {r s : Position m R} :
    baseline m R s ≤ baseline m R r - Δ / 2 ↔ posLT s r := by
  constructor
  · intro hs
    apply baseline_lt_iff.mp
    linarith
  · intro hsr
    have hgap := baseline_gap_of_posLT hsr
    linarith

theorem jobInterior_mem_current {Δ : ℚ} (hΔ : 0 < Δ) (r : Position m R) :
    baseline m R r - Δ ≤ baseline m R r - Δ / 2 ∧
      baseline m R r - Δ / 2 < baseline m R r := by
  constructor <;> linarith

theorem jobInterior_mem_job_iff {Δ : ℚ} (hΔ : 0 < Δ)
    (hΔg : Δ < gap m R) {r s : Position m R} :
    (baseline m R s - Δ ≤ baseline m R r - Δ / 2 ∧
      baseline m R r - Δ / 2 < baseline m R s) ↔ s = r := by
  constructor
  · rintro ⟨hleft, hright⟩
    rcases posLT_trichotomy s r with hsr | hsr | hrs
    · have hp := (baseline_le_jobInterior_iff hΔ hΔg).mpr hsr
      linarith
    · exact hsr
    · have hgap := baseline_gap_of_posLT hrs
      linarith
  · intro hsr
    subst s
    exact jobInterior_mem_current hΔ r

theorem baseline_le_actualJobInterior_iff (D L : ℕ) {r s : Position m R} :
    baseline m R s ≤ baseline m R r - delta m R D L / 2 ↔ posLT s r :=
  baseline_le_jobInterior_iff (delta_pos m R D L) (delta_lt_gap m R D L)

theorem actualJobInterior_mem_job_iff (D L : ℕ) {r s : Position m R} :
    (baseline m R s - delta m R D L ≤ baseline m R r - delta m R D L / 2 ∧
      baseline m R r - delta m R D L / 2 < baseline m R s) ↔ s = r :=
  jobInterior_mem_job_iff (delta_pos m R D L) (delta_lt_gap m R D L)

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TestGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

variable {m R D L : ℕ}

theorem jobInterior_mem_jobTestInterval (m R D L : ℕ) (r : Position m R) :
    jobInterior m R D L r ∈ jobTestInterval m R D L r :=
  jobInterior_mem_current (delta_pos m R D L) r

theorem jobInterior_mem_closedJobCell (m R D L : ℕ) (r : Position m R) :
    jobInterior m R D L r ∈ closedJobCell m R D L r :=
  jobTestInterval_subset_closedJobCell m R D L r
    (jobInterior_mem_jobTestInterval m R D L r)

theorem baseline_le_jobInterior (D L : ℕ) {r s : Position m R} :
    baseline m R s ≤ jobInterior m R D L r ↔ posLT s r :=
  baseline_le_actualJobInterior_iff D L

theorem jobInterior_mem_jobTestInterval_iff (D L : ℕ) {r s : Position m R} :
    jobInterior m R D L r ∈ jobTestInterval m R D L s ↔ s = r :=
  actualJobInterior_mem_job_iff D L

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingCoordinates
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

theorem globalLength_nonneg (u : D.GlobalCopy) : 0 ≤ D.globalLength u := by
  rcases u with ⟨s, i⟩
  cases s with
  | up b => cases b <;> norm_num [globalLength]
  | um b => cases b <;> norm_num [globalLength]
  | edge e b => simp [globalLength]

theorem globalLength_le_one (u : D.GlobalCopy) : D.globalLength u ≤ 1 := by
  rcases u with ⟨s, i⟩
  cases s with
  | up b => cases b <;> norm_num [globalLength]
  | um b => cases b <;> norm_num [globalLength]
  | edge e b => simp [globalLength]

end BinPackingGap.InventoryData

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

@[simp] theorem mem_tupleCovering (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (a : ℚ) (t : p.TableBin (subclass e)) :
    t ∈ tupleCovering p e v a ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
        tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t := by
  classical
  simp [tupleCovering, and_assoc]

theorem tupleGlobalLength_nonneg (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : 0 ≤ tupleGlobalLength p e t :=
  D.globalLength_nonneg _

theorem tupleGlobalLength_eq_of_unit_false (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hu : D.globalUnit (globalCopy p e t) = false) :
    tupleGlobalLength p e t = 0 := by
  have h : D.globalLength (globalCopy p e t) =
      if D.globalUnit (globalCopy p e t) then 1 else 0 := by
    rcases globalCopy p e t with ⟨s, i⟩
    cases s <;> rfl
  simpa only [tupleGlobalLength, hu, Bool.false_eq_true, ↓reduceIte] using h

private theorem localLength_nonneg {v : D.Vertex} (l : D.LocalAt v) : 0 ≤ D.localLength l := by
  rcases l with ((⟨ell, i⟩ | z) | g)
  · exact Geometry.lambda_nonneg _ _ _ _
  · rfl
  · rfl

theorem tupleLocalLength_nonneg (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : 0 ≤ tupleLocalLength p e t :=
  localLength_nonneg _

theorem tupleLocalLength_eq_zero_of_not_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v)
    (hnot : p.itemAtRole (subclass e) t .«local» ∉ positiveLocalResources e v) :
    tupleLocalLength p e t = 0 := by
  rcases hc : localCopy p e t with ⟨w, ((i | z) | g)⟩
  · have hw : w = v := by simpa only [hc] using good_local_vertex p e v t ht
    subst w
    exfalso
    apply hnot
    apply (mem_positiveLocalResources e v _).mpr
    refine ⟨i, ?_⟩
    rw [← roleCopy_item p e t .«local»]
    exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩) hc.symm
  · unfold tupleLocalLength
    rw [hc]
    rfl
  · unfold tupleLocalLength
    rw [hc]
    rfl

theorem tupleFinish_le_baseline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : tupleFinish p e t ≤ tupleBaseline p e t :=
  completion_le_baseline _ _ _ _ _ (tupleGlobalLength_nonneg p e t)
    (tupleLocalLength_nonneg p e t) (Geometry.delta_nonneg _ _ _ _)

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryPrefixConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

theorem packingInstance_size_eq (i : D.packingInstance.Item) :
    D.packingInstance.size i =
      encodedSize (D.encodedSubclass i) (D.encodedLabel i) (D.encodedCoordinate i) := rfl

end InventoryData

end

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_LocalCompletionCoverage
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open IntervalCoverage

variable (D : InventoryData)

theorem deadline_prefix_at_test (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (t : D.TestAt v) (a : ℚ) (ha : a ∈ D.testInterval t) :
    ((Finset.univ : Finset (D.MBase v)).filter (fun z => D.deadline z ≤ a)).card =
      ((Finset.univ : Finset (D.MBase v)).filter
        (fun z => D.mainBaseline z ≤ a)).card + D.d := by
  classical
  have hex : ∃ t : D.TestAt v, a ∈ D.testInterval t := ⟨t, ha⟩
  simpa only [prefixCount, prefixSet, ite_eq_left hex, Nat.mul_one] using
    D.deadline_prefix hplusheight hminusheight hL v a

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PackingExclusions
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem covering_not_selected_of_nonexcluded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v)
    (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)) :
    t ∉ zeroPositiveTuples p e v := by
  intro hselected
  apply hr
  apply (mem_excludedPositions _ _).mpr
  refine ⟨t, hselected, ?_⟩
  obtain ⟨_, hlo, hhi⟩ := (mem_tupleCovering p e v _ t).mp ht
  refine ⟨Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r,
    ⟨hlo, hhi.le⟩, ?_⟩
  exact Geometry.jobInterior_mem_closedJobCell _ _ _ _ _

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_InventoryRowGeometry
attribute [-instance] _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

private theorem node_right_in_root {T : UniformTree} (v : T.Node)
    (s : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    TreeGeometry.rootOffset s ≤
        TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ≤
        TreeGeometry.rootOffset s + 1 := by
  apply TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R D.geometryBound s hT v
  exact ⟨(TreeGeometry.left_lt_right _ _ _ _ _).le, le_rfl⟩

theorem rowBaseline_ge_four_of_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r = .tm) : 4 ≤ D.rowBaseline r := by
  rcases r with t | ⟨short, j⟩
  · rcases t with ⟨node, i⟩ | ⟨node, i⟩ | i
    · cases hclass
    · exact (D.node_right_in_root node .minus D.minus_branch_le_geometryBound).1
    · cases hclass
  · cases hclass

theorem rowShort_eq_false_of_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r = .tm) : D.rowShort r = false := by
  rcases r with t | ⟨short, j⟩
  · rfl
  · cases hclass

theorem exists_jobCopy_of_rowShort {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = true) : ∃ j : D.JobCopy v, r = .inr (true, j) := by
  rcases r with t | ⟨short, j⟩
  · cases hshort
  · change short = true at hshort
    subst short
    exact ⟨j, rfl⟩

theorem row_zero_resources_job {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = true) :
    ∃ j : D.JobCopy v, r = .inr (true, j) ∧
      D.rowPosition r = some (D.jobPosition j) ∧
      completionInterval (D.rowBaseline r) (D.rowShort r) 0 0
        (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) =
        Geometry.jobTestInterval D.graph.edges.length D.R D.geometryBound D.L
          (D.jobPosition j) := by
  obtain ⟨j, rfl⟩ := D.exists_jobCopy_of_rowShort r hshort
  refine ⟨j, rfl, rfl, ?_⟩
  exact completion_job_interval _ _ _ _ _

theorem minus_row_completion_gt_one {v w : D.Vertex} (r : D.RowAt v)
    (u : D.GlobalCopy) (l : D.LocalAt w) (hclass : D.rowSubclass r = .tm) :
    1 < completion (D.rowBaseline r) (D.rowShort r) (D.globalLength u)
      (D.localLength l) (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
  apply completion_minus_geometry_gt_one
    D.graph.edges.length D.R D.geometryBound D.L
  · exact D.rowBaseline_ge_four_of_tm r hclass
  · exact D.rowShort_eq_false_of_tm r hclass
  · exact D.globalLength_le_one u
  · exact D.localLength_le_lambda_one l

theorem minus_row_not_cover_jobInterior {v w : D.Vertex} (r : D.RowAt v)
    (u : D.GlobalCopy) (l : D.LocalAt w) (hclass : D.rowSubclass r = .tm)
    (job : D.Position) :
    Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L job ∉
      completionInterval (D.rowBaseline r) (D.rowShort r) (D.globalLength u)
        (D.localLength l) (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
  intro hmem
  have hh := D.minus_row_completion_gt_one r u l hclass
  have hj := (Geometry.closedJobCell_bounds
    (Geometry.jobInterior_mem_closedJobCell D.graph.edges.length D.R
      D.geometryBound D.L job)).2
  exact (not_le_of_gt (hj.trans hh)) hmem.1

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobCoverage
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem main_unit_species (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (hu : D.globalUnit (globalCopy p e t) = true) :
    (globalCopy p e t).1 = .up true ∨ (globalCopy p e t).1 = .um true := by
  rcases hcopy : globalCopy p e t with ⟨s, i⟩
  rw [hcopy] at hu
  change s = .up true ∨ s = .um true
  cases s with
  | up one =>
      change one = true at hu
      exact Or.inl (congrArg GlobalSpecies.up hu)
  | um one =>
      change one = true at hu
      exact Or.inr (congrArg GlobalSpecies.um hu)
  | edge edge permit =>
      have hglobal := roleCopy_subclass p e t .«global»
      change D.itemSubclass ⟨.«global», globalCopy p e t⟩ = _ at hglobal
      rw [hcopy] at hglobal
      have hmain := ((Coverage.mem_mainTuplesAt p (subclass e) (label e) v t).mp ht).2.2
      exfalso
      apply hmain
      cases hpattern : p.tablePattern (subclass e) t <;>
        rw [hpattern] at hglobal <;> cases hglobal

theorem row_minus_of_global_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hu : (globalCopy p e t).1 = .um true) :
    D.rowSubclass (rowCopy p e t).2 = .tm := by
  have hg := roleCopy_subclass p e t .«global»
  have hx := roleCopy_subclass p e t .x
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .um := by
    rcases hcopy : globalCopy p e t with ⟨s, i⟩
    have hs : s = .um true := by simpa only [hcopy] using hu
    subst s
    rfl
  have hpat : p.tablePattern (subclass e) t = .minusTree := by
    rw [hclass] at hg
    cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]
  rw [hpat] at hx
  change D.itemSubclass ⟨.x, rowCopy p e t⟩ = .tm at hx
  rcases hc : rowCopy p e t with ⟨w, r⟩
  rw [hc] at hx
  exact hx

theorem job_covering_global_not_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)) :
    (globalCopy p e t).1 ≠ .um true := by
  intro hu
  have hrow := row_minus_of_global_um p e t hu
  apply D.minus_row_not_cover_jobInterior (rowCopy p e t).2 (globalCopy p e t)
    (localCopy p e t).2 hrow r
  exact ((mem_tupleCovering p e v _ t).mp ht).2

theorem zero_resources_job_cover (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r))
    (hg : tupleGlobalLength p e t = 0) (hl : tupleLocalLength p e t = 0) :
    tupleBaseline p e t = Geometry.baseline D.graph.edges.length D.R r ∧
      tupleShort p e t = true := by
  have hmem := ((mem_tupleCovering p e v _ t).mp ht).2
  have hshort : tupleShort p e t = true := by
    cases hs : tupleShort p e t with
    | false =>
        have hfinish : tupleFinish p e t = tupleBaseline p e t := by
          simp [tupleFinish, hs, hg, hl]
        rw [hfinish] at hmem
        exact (not_lt_of_ge hmem.1 hmem.2).elim
    | true => rfl
  obtain ⟨j, hj, _, hinter⟩ := D.row_zero_resources_job (rowCopy p e t).2 hshort
  have hmem' : Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r ∈
      completionInterval (D.rowBaseline (rowCopy p e t).2)
        (D.rowShort (rowCopy p e t).2) 0 0
        (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
    change completion _ _ 0 0 _ ≤ _ ∧ _ < _
    simpa only [tupleFinish, hg, hl, tupleBaseline, tupleShort] using hmem
  rw [hinter] at hmem'
  have hpos : D.jobPosition j = r :=
    (Geometry.jobInterior_mem_jobTestInterval_iff D.geometryBound D.L).mp hmem'
  refine ⟨?_, hshort⟩
  simp only [tupleBaseline, hj, InventoryData.rowBaseline, hpos]

theorem nonexcluded_covering_subset (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v) :
    tupleCovering p e v (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r) ⊆
      fundedTuples p e (.up true) v ∪ shortMainAt p e v r := by
  classical
  intro t ht
  have hM := ((mem_tupleCovering p e v _ t).mp ht).1
  by_cases hu : D.globalUnit (globalCopy p e t) = true
  · have hspec := main_unit_species p e v t hM hu
    rcases hspec with hp | hm
    · exact Finset.mem_union_left _ ((mem_fundedTuples p e (.up true) v t).mpr
        ⟨hM, (selected_global_resource_iff p e t (.up true)).mpr hp⟩)
    · exact (job_covering_global_not_um p e v r t ht hm).elim
  · have hfalse : D.globalUnit (globalCopy p e t) = false := Bool.eq_false_of_not_eq_true hu
    have hnot := covering_not_selected_of_nonexcluded p e v r hr t ht
    have hnotpos : p.itemAtRole (subclass e) t .«local» ∉ positiveLocalResources e v := by
      intro hp
      exact hnot ((mem_zeroPositiveTuples p e v t).mpr ⟨hM, hfalse, hp⟩)
    have hlocal := tupleLocalLength_eq_zero_of_not_positive p e v t
      (Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v hM) hnotpos
    have hz := zero_resources_job_cover p e v r t ht
      (tupleGlobalLength_eq_of_unit_false p e t hfalse) hlocal
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hM, hz⟩)

theorem nonexcluded_coverage_upper (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v) :
    (tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)).card ≤
      xplus p e v + (shortMainAt p e v r).card := by
  calc
    _ ≤ (fundedTuples p e (.up true) v ∪ shortMainAt p e v r).card :=
      Finset.card_le_card (nonexcluded_covering_subset p e v r hr)
    _ ≤ _ := Finset.card_union_le _ _

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryCoverage
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap
namespace InventoryCoverage

variable {D : InventoryData} {I : Instance} {b : ℕ}

@[simp] theorem rowBaseline_selected (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) :
    rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) =
      D.rowBaseline (PackingCounts.rowCopy p e t).2 := by
  rw [← PackingCounts.roleCopy_item p e t .x]
  change itemRowBaseline D (e.symm (e ⟨.x, PackingCounts.rowCopy p e t⟩)) = _
  rw [e.symm_apply_apply]
  rfl

@[simp] theorem rowShort_selected (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) :
    rowShort e (p.itemAtRole (PackingCounts.subclass e) t .x) =
      D.rowShort (PackingCounts.rowCopy p e t).2 := by
  rw [← PackingCounts.roleCopy_item p e t .x]
  change itemRowShort D (e.symm (e ⟨.x, PackingCounts.rowCopy p e t⟩)) = _
  rw [e.symm_apply_apply]
  rfl

theorem keyBaseline_selected_of_key (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) (v : D.Vertex) (j : D.JobCopy v)
    (hcopy : PackingCounts.anchorCopy p e t = ⟨v, .inr j⟩) :
    keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor) =
      Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) := by
  rw [← PackingCounts.roleCopy_item p e t .anchor]
  change itemKeyBaseline D (e.symm (e ⟨.anchor, PackingCounts.anchorCopy p e t⟩)) = _
  rw [e.symm_apply_apply, hcopy]
  rfl

theorem anchorDeadline_selected_of_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) (v : D.Vertex) (z : D.MBase v)
    (hcopy : PackingCounts.anchorCopy p e t = ⟨v, .inl z⟩) :
    anchorDeadline e (p.itemAtRole (PackingCounts.subclass e) t .anchor) = D.deadline z := by
  rw [← PackingCounts.roleCopy_item p e t .anchor]
  change itemDeadline D (e.symm (e ⟨.anchor, PackingCounts.anchorCopy p e t⟩)) = _
  rw [e.symm_apply_apply, hcopy]
  rfl

theorem rowShort_implies_job (e : D.Item ≃ I.Item) (i : I.Item)
    (h : rowShort e i = true) : PackingCounts.subclass e i = .s := by
  let x := e.symm i
  change itemRowShort D x = true at h
  change D.itemSubclass x = .s
  rcases x with ⟨role, copy⟩
  cases role with
  | x =>
      rcases copy with ⟨v, tree | ⟨short, job⟩⟩
      · cases h
      · rfl
  | anchor => cases h
  | «global» => cases h
  | «local» => cases h
  | flag => cases h

private theorem treeSubclass_ne_s (t : D.TreeRow) : D.treeSubclass t ≠ .s := by
  rcases t with p | (m | pad) <;> simp [InventoryData.treeSubclass]

private theorem treeSubclass_tree (t : D.TreeRow) :
    D.treeSubclass t = .tp ∨ D.treeSubclass t = .tm := by
  rcases t with p | (m | pad)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem card_filter_transport {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun x => P (e x)).card := by
  exact (Finset.card_bijective (s := Finset.univ.filter fun x => P (e x))
    (t := Finset.univ.filter P) e e.bijective (fun _ => by simp)).symm

set_option maxHeartbeats 1000000 in
theorem jobRowPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.jobRowPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card = 2 * (jobPrefix D v a).card := by
  classical
  unfold Coverage.jobRowPrefixAt
  rw [card_filter_transport e]
  simp only [jobPrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, itemRowBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.rowBaseline, treeSubclass_ne_s,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type, two_mul]

theorem treeRowPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.treeRowPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card = (treePrefix D a).card := by
  classical
  unfold Coverage.treeRowPrefixAt
  rw [card_filter_transport e]
  simp only [treePrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, itemRowBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.rowBaseline, treeSubclass_tree,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem keyPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.keyPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (keyBaseline e) a).card = (jobPrefix D v a).card := by
  classical
  unfold Coverage.keyPrefixAt
  rw [card_filter_transport e]
  simp only [jobPrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, keyBaseline, itemKeyBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem deadlinePrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.deadlinePrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (anchorDeadline e) a).card =
      (Finset.univ.filter fun z : D.MBase v => D.deadline z ≤ a).card := by
  classical
  unfold Coverage.deadlinePrefixAt
  rw [card_filter_transport e]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, anchorDeadline, itemDeadline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem originalBaselinePrefix_card (D : InventoryData) (v : D.Vertex) (a : ℚ) :
    (originalBaselinePrefix D v a).card = (treePrefix D a).card + (jobPrefix D v a).card := by
  classical
  have hsplit : originalBaselinePrefix D v a =
      (treePrefix D a).disjSum (jobPrefix D v a) := by
    ext z
    cases z <;>
      simp only [originalBaselinePrefix, treePrefix, jobPrefix, Finset.mem_filter,
        Finset.mem_univ, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, true_and] <;>
      rfl
  rw [hsplit, Finset.card_disjSum]

theorem currentKeyItems_card (e : D.Item ≃ I.Item) (v : D.Vertex) (current : ℚ) :
    (Coverage.currentKeyItemsAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (keyBaseline e) current).card = (jobsAt D v current).card := by
  classical
  unfold Coverage.currentKeyItemsAt
  rw [card_filter_transport e]
  simp only [jobsAt, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, keyBaseline, itemKeyBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem currentShortItems_card (e : D.Item ≃ I.Item) (v : D.Vertex) (current : ℚ) :
    (Coverage.currentShortItemsAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (rowShort e) current).card = (jobsAt D v current).card := by
  classical
  unfold Coverage.currentShortItemsAt
  rw [card_filter_transport e]
  simp only [jobsAt, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, rowShort,
    itemRowBaseline, itemRowShort, InventoryData.itemSubclass, InventoryData.itemLabel,
    InventoryData.RoleCopies, InventoryData.rowSubclass, InventoryData.rowBaseline,
    InventoryData.rowShort, treeSubclass_ne_s,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem positionOf_injective (D : InventoryData) (v : D.Vertex) :
    Function.Injective (positionOf D (v := v)) :=
  D.incidencePosition_injective v

theorem job_baseline_eq_iff (D : InventoryData) (v : D.Vertex)
    (j : D.JobCopy v) (r : D.IncidencePosition v) :
    Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) =
      Geometry.baseline D.graph.edges.length D.R (positionOf D r) ↔ j.1 = r := by
  rw [Geometry.baseline_eq_iff]
  change positionOf D j.1 = positionOf D r ↔ j.1 = r
  exact (positionOf_injective D v).eq_iff

theorem jobsAt_position_card (D : InventoryData) (v : D.Vertex)
    (r : D.IncidencePosition v) :
    (jobsAt D v (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card = D.d := by
  classical
  have heq : jobsAt D v (Geometry.baseline D.graph.edges.length D.R (positionOf D r)) =
      ({r} : Finset (D.IncidencePosition v)).product (Finset.univ : Finset (Fin D.d)) := by
    ext ⟨s, j⟩
    simp only [jobsAt, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton, and_true]
    exact job_baseline_eq_iff D v (s, j) r
  rw [heq]
  simp

theorem actual_displaced_baseline_prefix_le
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ)
    (extra : Finset (p.TableBin (PackingCounts.subclass e))) (K : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hextra : extra ⊆ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v)
    (hextraRows : ∀ t ∈ extra, rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤ a)
    (hextraDis : Disjoint
      (Coverage.edgePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
        (keyBaseline e) a) extra) :
    (Coverage.baselinePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card + extra.card ≤ (originalBaselinePrefix D v a).card + 3 * K := by
  apply Coverage.displaced_baseline_prefix_le p (PackingCounts.subclass e) (PackingCounts.label e) v
    (rowBaseline e) (keyBaseline e) a extra (originalBaselinePrefix D v a).card
    (jobPrefix D v a).card K hbad horder hextra hextraRows hextraDis
  · exact jobRowPrefix_card e v a
  · exact keyPrefix_card e v a
  · rw [treeRowPrefix_card, originalBaselinePrefix_card]

private theorem exists_job_of_subclass_s (D : InventoryData) (i : D.Item)
    (h : D.itemSubclass i = .s) :
    ∃ v : D.Vertex, ∃ short : Bool, ∃ j : D.JobCopy v,
      i = ⟨.x, ⟨v, .inr (short, j)⟩⟩ := by
  have hr : i.1 = .x := by
    change D.itemRole i = .x
    rw [← D.itemSubclass_role, h]
    rfl
  rcases i with ⟨role, copy⟩
  dsimp at hr
  subst role
  rcases copy with ⟨v, tree | ⟨short, job⟩⟩
  · exact False.elim (treeSubclass_ne_s tree h)
  · exact ⟨v, short, job, rfl⟩

theorem row_before_current_le_interior (e : D.Item ≃ I.Item) (i : I.Item)
    (hcls : PackingCounts.subclass e i = .s) {v : D.Vertex}
    (r : D.IncidencePosition v)
    (hearlier : rowBaseline e i <
      Geometry.baseline D.graph.edges.length D.R (positionOf D r)) :
    rowBaseline e i ≤
      Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r) := by
  obtain ⟨w, short, j, hj⟩ := exists_job_of_subclass_s D (e.symm i) hcls
  have hbase : rowBaseline e i =
      Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) := by
    change itemRowBaseline D (e.symm i) = _
    rw [hj]
    rfl
  rw [hbase] at hearlier ⊢
  exact (Geometry.baseline_le_jobInterior D.geometryBound D.L).mpr
    (Geometry.baseline_lt_iff.mp hearlier)

theorem actual_displaced_job_prefix_le
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex)
    (r : D.IncidencePosition v) (K : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor)) :
    (Coverage.baselinePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e)
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r))).card +
    (Coverage.displacedTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (keyBaseline e)
      (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card ≤
    (originalBaselinePrefix D v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r))).card +
      3 * K := by
  classical
  apply actual_displaced_baseline_prefix_le p e v _ _ K hbad horder
  · intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  · intro t ht
    obtain ⟨ht, hbefore⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    have hpat := ((Coverage.mem_edgeTuplesAt p (PackingCounts.subclass e)
      (PackingCounts.label e) v t).mp ht).2.2
    apply row_before_current_le_interior e _ _ r hbefore
    rw [p.itemAtRole_subclass (PackingCounts.subclass e) t .x, hpat]
    rfl
  · apply Finset.disjoint_left.mpr
    intro t hearly hcurrent
    have hle := (Finset.mem_filter.mp hearly).2
    have heq := (Finset.mem_filter.mp (Finset.mem_filter.mp hcurrent).1).2
    rw [heq] at hle
    have hcut := (Geometry.jobInterior_mem_jobTestInterval D.graph.edges.length D.R
      D.geometryBound D.L (positionOf D r)).2
    exact (not_lt_of_ge hle) hcut

theorem actual_current_long_matches_from_correction
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex)
    (r : D.IncidencePosition v) (K xplus : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hcorrection : D.d + (Coverage.displacedTuplesAt p (PackingCounts.subclass e)
        (PackingCounts.label e) v (rowBaseline e) (keyBaseline e)
        (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card ≤
      xplus + (Coverage.currentShortMainAt p (PackingCounts.subclass e)
        (PackingCounts.label e) v (rowBaseline e) (rowShort e)
        (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card + 6 * K) :
    D.d ≤ (Coverage.currentLongEdgeAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (keyBaseline e) (rowShort e)
      (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card + xplus + 9 * K := by
  apply Coverage.current_long_matches_from_correction p (PackingCounts.subclass e)
    (PackingCounts.label e) v (rowBaseline e) (keyBaseline e) (rowShort e)
    (Geometry.baseline D.graph.edges.length D.R (positionOf D r)) D.d K xplus
    hbad horder (rowShort_implies_job e) _ _ hcorrection
  · rw [currentKeyItems_card, jobsAt_position_card]
  · rw [currentShortItems_card, jobsAt_position_card]

end InventoryCoverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_KeyGeometry
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

theorem keyExpression_eq_coordinates (m R D L : ℕ) (row key : Position m R)
    (edge : Fin m) (nonpermit short : Bool) :
    keyExpression m R D L row key edge nonpermit short =
      (baseline m R row - if short then delta m R D L else 0) +
      (-baseline m R key - beta m R key.1) +
      (beta m R edge + if nonpermit then delta m R D L else 0) + 0 + 0 := by
  cases nonpermit <;> cases short <;> simp [keyExpression] <;> ring

theorem key_perturbation_lower (m R D L : ℕ) (nonpermit short : Bool) :
    -delta m R D L ≤
      delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0)) := by
  have hd := delta_nonneg m R D L
  cases nonpermit <;> cases short <;> simp_all

theorem keyExpression_pos_of_later_row {m R D L : ℕ}
    {row key : Position m R} (edge : Fin m) (nonpermit short : Bool)
    (hlater : posLT key row) :
    0 < keyExpression m R D L row key edge nonpermit short := by
  have hg := gap_pos m R
  have hd := delta_lt_gap m R D L
  have hjump := mul_le_mul_of_nonneg_left (heightCode_jump hlater) (le_of_lt hg)
  have hedge := mul_nonneg (le_of_lt hg) (theta_nonneg R edge)
  have hpert := key_perturbation_lower m R D L nonpermit short
  dsimp [keyExpression, baseline, beta]
  nlinarith

theorem keyExpression_pos_of_later_edge {m R D L : ℕ}
    (row key : Position m R) {edge : Fin m} (nonpermit short : Bool)
    (hlater : key.1 < edge) :
    0 < keyExpression m R D L row key edge nonpermit short := by
  have hg := gap_pos m R
  have hd := delta_lt_gap m R D L
  have hjump := mul_le_mul_of_nonneg_left
    (theta_jump_ge_heightCode (R := R) hlater) (le_of_lt hg)
  have hrow := mul_nonneg (le_of_lt hg) (heightCode_nonneg R row)
  have hpert := key_perturbation_lower m R D L nonpermit short
  dsimp [keyExpression, baseline, beta]
  nlinarith

theorem row_order_of_key_feasible {m R D L : ℕ}
    {row key : Position m R} {edge : Fin m} {nonpermit short : Bool}
    (h : keyExpression m R D L row key edge nonpermit short ≤ 0) :
    posLE row key := by
  apply posLE_iff_not_posLT.mpr
  intro hlater
  exact (not_lt_of_ge h) (keyExpression_pos_of_later_row edge nonpermit short hlater)

theorem edge_order_of_key_feasible {m R D L : ℕ}
    {row key : Position m R} {edge : Fin m} {nonpermit short : Bool}
    (h : keyExpression m R D L row key edge nonpermit short ≤ 0) :
    edge ≤ key.1 := by
  by_contra hnot
  exact (not_lt_of_ge h)
    (keyExpression_pos_of_later_edge row key nonpermit short (lt_of_not_ge hnot))

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingFeasibility
attribute [-instance] _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

open scoped BigOperators

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem good_selected_labels (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) (r : Role) :
    label e (p.itemAtRole (subclass e) t r) = tableRoleLabel v v v r := by
  cases r with
  | x =>
      simpa only [selected_row_label, tableRoleLabel] using
        congrArg some (good_row_vertex p e v t ht)
  | anchor =>
      simpa only [selected_anchor_label, tableRoleLabel] using
        congrArg some (good_anchor_vertex p e v t ht)
  | «global» =>
      change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .«global»)) = none
      rw [← roleCopy_item p e t .«global», e.symm_apply_apply]
      rfl
  | «local» =>
      simpa only [selected_local_label, tableRoleLabel] using
        congrArg some (good_local_vertex p e v t ht)
  | flag =>
      change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .flag)) = none
      rw [← roleCopy_item p e t .flag, e.symm_apply_apply]
      rfl

@[simp] theorem selected_itemCoordinate (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemCoordinate (e.symm (p.itemAtRole (subclass e) t r)) =
      D.itemCoordinate ⟨r, roleCopy p e t r⟩ := by
  rw [← roleCopy_item p e t r]
  simp only [Equiv.symm_apply_apply]

theorem good_coordinate_nonpos (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    D.rowCoordinate (rowCopy p e t).2 + D.anchorCoordinate (anchorCopy p e t).2 +
      D.globalCoordinate (globalCopy p e t) + D.localCoordinate (localCopy p e t).2 ≤ 0 := by
  have h := p.table_coordinate_nonpos_of_same_label (subclass e) (label e)
    (fun i => D.itemCoordinate (e.symm i)) hsize t v (good_selected_labels p e v t ht)
  simp only [selected_itemCoordinate] at h
  rw [Role.sum_univ] at h
  have hx (x : Σ v : D.Vertex, D.RowAt v) :
      D.itemCoordinate ⟨.x, x⟩ = D.rowCoordinate x.2 := by
    cases x
    rfl
  have ha (a : Σ v : D.Vertex, D.AnchorAt v) :
      D.itemCoordinate ⟨.anchor, a⟩ = D.anchorCoordinate a.2 := by
    cases a
    rfl
  have hl (l : Σ v : D.Vertex, D.LocalAt v) :
      D.itemCoordinate ⟨.«local», l⟩ = D.localCoordinate l.2 := by
    cases l
    rfl
  rw [hx (rowCopy p e t), ha (anchorCopy p e t), hl (localCopy p e t)] at h
  simpa only [InventoryData.itemCoordinate, add_zero] using h

private theorem main_anchor_of_subclass (a : Σ v : D.Vertex, D.AnchorAt v)
    (h : D.itemSubclass ⟨.anchor, a⟩ = .z) :
    ∃ z : D.MBase a.1, a.2 = .inl z := by
  rcases a with ⟨v, z | j⟩
  · exact ⟨z, rfl⟩
  · simp [InventoryData.itemSubclass] at h

private theorem globalCoordinate_of_not_w (u : D.GlobalCopy)
    (h : D.itemSubclass ⟨.«global», u⟩ ≠ .w) :
    D.globalCoordinate u = -D.globalLength u := by
  rcases u with ⟨species, i⟩
  cases species with
  | up one => rfl
  | um one => rfl
  | edge edge permit => exact (h rfl).elim

theorem main_anchor_copy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t ≠ .edgeJob) :
    ∃ z : D.MBase (anchorCopy p e t).1, (anchorCopy p e t).2 = .inl z := by
  apply main_anchor_of_subclass
  have h := roleCopy_subclass p e t .anchor
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

theorem main_globalCoordinate (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t ≠ .edgeJob) :
    D.globalCoordinate (globalCopy p e t) = -D.globalLength (globalCopy p e t) := by
  apply globalCoordinate_of_not_w
  have h := roleCopy_subclass p e t .«global»
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

theorem main_completion_le_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v) :
    ∃ z : D.MBase (anchorCopy p e t).1,
      (anchorCopy p e t).2 = .inl z ∧ tupleFinish p e t ≤ D.deadline z := by
  have hpat := ((Coverage.mem_mainTuplesAt p (subclass e) (label e) v t).mp ht).2.2
  have hgood := Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v ht
  have h := good_coordinate_nonpos p e hsize v t hgood
  obtain ⟨z, hz⟩ := main_anchor_copy p e t hpat
  refine ⟨z, hz, ?_⟩
  have ha : D.anchorCoordinate (anchorCopy p e t).2 = -D.deadline z := by
    rw [hz]
    rfl
  rw [ha, main_globalCoordinate p e t hpat] at h
  change D.rowCoordinate (rowCopy p e t).2 + -D.deadline z +
    -D.globalLength (globalCopy p e t) + -D.localLength (localCopy p e t).2 ≤ 0 at h
  have rearrange (x deadline globalLen localLen : ℚ)
      (hh : x + -deadline + -globalLen + -localLen ≤ 0) :
      x - globalLen - localLen ≤ deadline := by linarith
  exact rearrange (D.rowCoordinate (rowCopy p e t).2) (D.deadline z)
    (D.globalLength (globalCopy p e t)) (D.localLength (localCopy p e t).2) h

theorem main_completion_le_selected_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v) :
    tupleFinish p e t ≤
      InventoryCoverage.anchorDeadline e (p.itemAtRole (subclass e) t .anchor) := by
  obtain ⟨z, hz, hfinish⟩ := main_completion_le_deadline p e hsize v t ht
  have hcopy : anchorCopy p e t = ⟨(anchorCopy p e t).1, .inl z⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p e t)]
    rw [hz]
  rw [InventoryCoverage.anchorDeadline_selected_of_deadline p e t _ z hcopy]
  exact hfinish

private theorem job_row_of_subclass (a : Σ v : D.Vertex, D.RowAt v)
    (h : D.itemSubclass ⟨.x, a⟩ = .s) :
    ∃ short : Bool, ∃ j : D.JobCopy a.1, a.2 = .inr (short, j) := by
  rcases a with ⟨v, row | ⟨short, j⟩⟩
  · rcases row with plus | (minus | padding) <;>
      simp [InventoryData.itemSubclass, InventoryData.rowSubclass,
        InventoryData.treeSubclass] at h
  · exact ⟨short, j, rfl⟩

private theorem key_anchor_of_subclass (a : Σ v : D.Vertex, D.AnchorAt v)
    (h : D.itemSubclass ⟨.anchor, a⟩ = .y) :
    ∃ j : D.JobCopy a.1, a.2 = .inr j := by
  rcases a with ⟨v, z | j⟩
  · simp [InventoryData.itemSubclass] at h
  · exact ⟨j, rfl⟩

private theorem edge_global_of_subclass (u : D.GlobalCopy)
    (h : D.itemSubclass ⟨.«global», u⟩ = .w) :
    ∃ edge : D.Edge, ∃ permit : Bool, ∃ i : Fin (D.globalStock (.edge edge permit)),
      u = ⟨.edge edge permit, i⟩ := by
  rcases u with ⟨species, i⟩
  cases species with
  | up one => simp [InventoryData.itemSubclass] at h
  | um one => simp [InventoryData.itemSubclass] at h
  | edge edge permit => exact ⟨edge, permit, i, rfl⟩

private theorem edge_local_of_subclass (a : Σ v : D.Vertex, D.LocalAt v)
    (h : D.itemSubclass ⟨.«local», a⟩ = .dg) :
    ∃ j : D.JobCopy a.1, a.2 = .inr j := by
  rcases a with ⟨v, main | j⟩
  · simp [InventoryData.itemSubclass] at h
  · exact ⟨j, rfl⟩

theorem edgeTupleData_nonempty (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t = .edgeJob) :
    Nonempty (EdgeTupleData p e t) := by
  have hx : D.itemSubclass ⟨.x, rowCopy p e t⟩ = .s := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .x
  have ha : D.itemSubclass ⟨.anchor, anchorCopy p e t⟩ = .y := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .anchor
  have hu : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .w := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .«global»
  have hl : D.itemSubclass ⟨.«local», localCopy p e t⟩ = .dg := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .«local»
  obtain ⟨short, row, hrow⟩ := job_row_of_subclass _ hx
  obtain ⟨key, hkey⟩ := key_anchor_of_subclass _ ha
  obtain ⟨edge, permit, i, hglobal⟩ := edge_global_of_subclass _ hu
  obtain ⟨localJob, hlocal⟩ := edge_local_of_subclass _ hl
  exact ⟨⟨short, row, key, localJob, edge, permit, i, hrow, hkey, hlocal, hglobal⟩⟩

namespace EdgeTupleData

variable {p : Packing I b} {e : D.Item ≃ I.Item} {t : p.TableBin (subclass e)}

theorem expression_eq_coordinates (w : EdgeTupleData p e t) :
    w.expression =
      D.rowCoordinate (rowCopy p e t).2 + D.anchorCoordinate (anchorCopy p e t).2 +
        D.globalCoordinate (globalCopy p e t) + D.localCoordinate (localCopy p e t).2 := by
  rw [w.row_eq, w.anchor_eq, w.global_eq, w.local_eq]
  unfold expression
  rw [Geometry.keyExpression_eq_coordinates]
  simp only [InventoryData.rowCoordinate, InventoryData.rowBaseline, InventoryData.rowShort,
    InventoryData.anchorCoordinate, InventoryData.globalCoordinate,
    InventoryData.localCoordinate, InventoryData.localLength, neg_zero, add_zero]
  cases w.permit <;> cases w.short <;> simp

theorem feasible (w : EdgeTupleData p e t)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    w.expression ≤ 0 := by
  rw [w.expression_eq_coordinates]
  exact good_coordinate_nonpos p e hsize v t ht

theorem row_order (w : EdgeTupleData p e t) (h : w.expression ≤ 0) :
    Geometry.posLE (D.jobPosition w.row) (D.jobPosition w.key) :=
  Geometry.row_order_of_key_feasible h

theorem edge_order (w : EdgeTupleData p e t) (h : w.expression ≤ 0) :
    w.edge ≤ (D.jobPosition w.key).1 :=
  Geometry.edge_order_of_key_feasible h

end EdgeTupleData

theorem edge_tuple_feasible (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.edgeTuplesAt p (subclass e) (label e) v) :
    ∃ w : EdgeTupleData p e t, w.expression ≤ 0 ∧
      Geometry.posLE (D.jobPosition w.row) (D.jobPosition w.key) ∧
        w.edge ≤ (D.jobPosition w.key).1 := by
  have hpat := ((Coverage.mem_edgeTuplesAt p (subclass e) (label e) v t).mp ht).2.2
  obtain ⟨w⟩ := edgeTupleData_nonempty p e t hpat
  have hf := w.feasible hsize v
    (Coverage.edgeTuplesAt_subset_good p (subclass e) (label e) v ht)
  exact ⟨w, hf, w.row_order hf, w.edge_order hf⟩

theorem edge_selected_baseline_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.edgeTuplesAt p (subclass e) (label e) v) :
    InventoryCoverage.rowBaseline e (p.itemAtRole (subclass e) t .x) ≤
      InventoryCoverage.keyBaseline e (p.itemAtRole (subclass e) t .anchor) := by
  obtain ⟨w, _, hrow, _⟩ := edge_tuple_feasible p e hsize v t ht
  have hcopy : anchorCopy p e t = ⟨(anchorCopy p e t).1, .inr w.key⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p e t)]
    rw [w.anchor_eq]
  rw [InventoryCoverage.rowBaseline_selected,
    InventoryCoverage.keyBaseline_selected_of_key p e t _ w.key hcopy, w.row_eq]
  exact Geometry.baseline_le_iff.mpr hrow

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_CoverageSoundness
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

namespace InventoryCoverage

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem coveringTuplesAt_eq (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (a : ℚ) :
    Coverage.coveringTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (PackingCounts.tupleFinish p e) a =
      PackingCounts.tupleCovering p e v a := by
  unfold Coverage.coveringTuplesAt PackingCounts.tupleCovering
  apply Finset.filter_congr
  intro t _
  rw [rowBaseline_selected p e t]
  rfl

theorem shortMainAt_eq (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) :
    Coverage.currentShortMainAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (rowShort e) (Geometry.baseline D.graph.edges.length D.R r) =
      PackingCounts.shortMainAt p e v r := by
  unfold Coverage.currentShortMainAt PackingCounts.shortMainAt
  apply Finset.filter_congr
  intro t _
  rw [rowBaseline_selected p e t, rowShort_selected p e t]
  rfl

end InventoryCoverage

namespace InventoryData

variable (D : InventoryData)

theorem long_matches_at_nonexcluded_oaiq082_oai {b c : ℕ}
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (v : D.Vertex) (r : D.IncidencePosition v)
    (hr : D.incidencePosition r ∉ PackingCounts.excludedAt p D.itemEquiv v) :
    D.d ≤ D.longMatchesAt p v r + PackingCounts.xplus p D.itemEquiv v + 9 * lossAllowance c := by
  classical
  let a := Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (D.incidencePosition r)
  let finish := PackingCounts.tupleFinish p D.itemEquiv
  have hbad := D.badAnchorsAt_card_le_oaiq082 hk p hb v
  have horder := PackingCounts.edge_selected_baseline_le p D.itemEquiv
    D.packingInstance_size_eq v
  have hle : ∀ u ∈ Coverage.mainTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v,
      finish u ≤ InventoryCoverage.rowBaseline D.itemEquiv
        (p.itemAtRole (PackingCounts.subclass D.itemEquiv) u .x) := by
    intro u _
    simpa only [finish, InventoryCoverage.rowBaseline_selected, PackingCounts.tupleBaseline] using
      PackingCounts.tupleFinish_le_baseline p D.itemEquiv u
  have hfeasible := PackingCounts.main_completion_le_selected_deadline p D.itemEquiv
    D.packingInstance_size_eq v
  have hpartition := Coverage.completion_prefix_decomposition p (PackingCounts.subclass D.itemEquiv)
    (PackingCounts.label D.itemEquiv) v (InventoryCoverage.rowBaseline D.itemEquiv) finish hle a
  have hdeadline := Coverage.deadline_prefix_le_completion_add_loss p (PackingCounts.subclass D.itemEquiv)
    (PackingCounts.label D.itemEquiv) v (InventoryCoverage.anchorDeadline D.itemEquiv) finish a
    (lossAllowance c) hbad hfeasible
  have ha : a ∈ D.testInterval (.inr (.inr r) : D.TestAt v) :=
    Geometry.jobInterior_mem_jobTestInterval D.graph.edges.length D.R D.geometryBound D.L
      (D.incidencePosition r)
  rw [InventoryCoverage.deadlinePrefix_card,
    D.deadline_prefix_at_test hplusheight hminusheight hL v (.inr (.inr r)) a ha] at hdeadline
  have hbase := InventoryCoverage.actual_displaced_job_prefix_le p D.itemEquiv v r
    (lossAllowance c) hbad horder
  have hupper : (Coverage.coveringTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v
      (InventoryCoverage.rowBaseline D.itemEquiv) finish a).card ≤
      PackingCounts.xplus p D.itemEquiv v +
      (Coverage.currentShortMainAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v
        (InventoryCoverage.rowBaseline D.itemEquiv) (InventoryCoverage.rowShort D.itemEquiv)
        (Geometry.baseline D.graph.edges.length D.R (D.incidencePosition r))).card := by
    simpa only [finish, a, InventoryCoverage.coveringTuplesAt_eq,
      InventoryCoverage.shortMainAt_eq] using
      PackingCounts.nonexcluded_coverage_upper p D.itemEquiv v (D.incidencePosition r) hr
  have hcorrection := CoverageCounts.displaced_short_correction hpartition hdeadline hbase hupper
  exact InventoryCoverage.actual_current_long_matches_from_correction p D.itemEquiv v r
    (lossAllowance c) (PackingCounts.xplus p D.itemEquiv v) hbad horder hcorrection

end InventoryData
end BinPackingGap

end

end OAI
end

theorem solution : type_of% @OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded_oaiq082_oai := @OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded_oaiq082_oai
