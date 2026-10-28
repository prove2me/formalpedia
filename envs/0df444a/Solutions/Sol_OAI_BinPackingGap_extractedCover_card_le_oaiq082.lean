-- Prove2me | solution 1 for OAI.BinPackingGap.extractedCover_card_le_oaiq082
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:11:21.830865+00:00
-- url     : https://prove2.me/submissions/05a007c5-d3f0-4c0d-894a-b68a2b251839

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C021
import Definitions.Def_OAIQ082C022
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

theorem lambda_add_delta_lt_three (m R D : ℕ) {ell L : ℕ} (h : ell ≤ L) :
    lambda m R D ell + delta m R D L < 3 * lambda m R D ell := by
  have hd := delta_le_tenth m R D h
  have hl := lambda_pos m R D ell
  linarith

end BinPackingGap.Geometry

namespace BinPackingGap

theorem completion_le_baseline (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ)
    (hglobal : 0 ≤ globalLen) (hlocal : 0 ≤ localLen) (hdelta : 0 ≤ delta) :
    completion b short globalLen localLen delta ≤ b := by
  cases short <;> simp only [completion_false, completion_true] <;> linarith

theorem completion_zero_global_length_le (b : ℚ) (short : Bool) (localLen delta : ℚ)
    (hdelta : 0 ≤ delta) :
    b - completion b short 0 localLen delta ≤ localLen + delta := by
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

theorem goodTuplesAt_disjoint_label (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (goodTuplesAt p cls label v) (goodTuplesAt p cls label w) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  have hv := ((mem_goodTuplesAt p cls label v t).mp ht).2
  have hw := ((mem_goodTuplesAt p cls label w t).mp hu).2
  exact hvw (Option.some.inj (hv.symm.trans hw))

theorem mainTuplesAt_disjoint_label (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (mainTuplesAt p cls label v) (mainTuplesAt p cls label w) :=
  (goodTuplesAt_disjoint_label p cls label hvw).mono
    (mainTuplesAt_subset_good p cls label v) (mainTuplesAt_subset_good p cls label w)

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

end Coverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_K4Graph
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype _root_.OAI.BinPackingGap.instFintypeGlobalSpecies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

theorem depthDemand_ge_120_div (c : ℕ) (ρ : ℝ) :
    120 * (lossAllowance c : ℝ) / ρ ≤ (depthDemand c ρ : ℝ) := by
  exact (le_max_right _ _).trans (Nat.le_ceil _)

theorem threshold_gap {d K : ℝ} (hd : 0 < d) (h72 : 72 * K ≤ d) :
    d / 8 < d - 6 * K := by
  linarith

theorem sixty_loss_div_le {ρ d K n : ℝ} (hρ : 0 < ρ) (hd : 0 < d)
    (hK : 0 ≤ K) (hn : 0 ≤ n) (h120 : 120 * K / ρ ≤ d) :
    60 * K * n / d ≤ ρ * n := by
  have hmul := (div_le_iff₀ hρ).mp h120
  have h60 : 60 * K ≤ ρ * d := by nlinarith
  apply (div_le_iff₀ hd).mpr
  calc
    60 * K * n ≤ (ρ * d) * n := mul_le_mul_of_nonneg_right h60 hn
    _ = (ρ * n) * d := by ring

open scoped BigOperators

end BinPackingGap

section
open scoped BigOperators

namespace BinPackingGap

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem residual_plus_le {d K : ℕ} (xplus xminus : V → ℕ)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    (∑ v, if v ∈ largePlus d K xplus then (0 : ℝ) else (xplus v : ℝ)) ≤
      6 * (K : ℝ) * Fintype.card V := by
  classical
  let charge : V → ℝ := fun v =>
    if v ∈ largePlus d K xplus then (xplus v : ℝ) else (xminus v : ℝ)
  let rest : V → ℝ := fun v =>
    if v ∈ largePlus d K xplus then 0 else (xplus v : ℝ)
  have hcharge : ∀ v, (d : ℝ) - 6 * K ≤ charge v := by
    intro v
    by_cases hv : v ∈ largePlus d K xplus
    · simpa only [charge, ite_eq_left hv] using (Finset.mem_filter.mp hv).2
    · have hnot : ¬ ((d : ℝ) - 6 * K ≤ (xplus v : ℝ)) := by
        simpa [largePlus] using hv
      rcases hside v with hp | hm
      · have hp' : (d : ℝ) ≤ (xplus v : ℝ) + 6 * K := by exact_mod_cast hp
        exact (hnot (by linarith)).elim
      · have hm' : (d : ℝ) ≤ (xminus v : ℝ) + 6 * K := by exact_mod_cast hm
        simp only [charge, ite_eq_right hv]
        linarith
  have hcharged : (Fintype.card V : ℝ) * ((d : ℝ) - 6 * K) ≤ ∑ v, charge v := by
    calc
      _ = ∑ _v : V, ((d : ℝ) - 6 * K) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ v, charge v := Finset.sum_le_sum fun v _ => hcharge v
  have hpoint : ∀ v, charge v + rest v ≤ (xplus v : ℝ) + xminus v := by
    intro v
    dsimp only [charge, rest]
    split_ifs <;> nlinarith [show (0 : ℝ) ≤ xplus v from Nat.cast_nonneg _,
      show (0 : ℝ) ≤ xminus v from Nat.cast_nonneg _]
  have hsum : (∑ v, charge v) + (∑ v, rest v) ≤
      (d : ℝ) * Fintype.card V := by
    calc
      _ = ∑ v, (charge v + rest v) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ v, ((xplus v : ℝ) + xminus v) := Finset.sum_le_sum fun v _ => hpoint v
      _ ≤ (d : ℝ) * Fintype.card V := by exact_mod_cast htotal
  change (∑ v, rest v) ≤ _
  nlinarith

theorem thresholdCover_card_le_fractions {d K k : ℕ} (xplus xminus : V → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤
      (d : ℝ) * k / ((d : ℝ) - 6 * K) + 48 * (K : ℝ) * Fintype.card V / d := by
  classical
  let A := largePlus d K xplus
  let C := thresholdCover d xplus
  let B := C \ A
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  have hgap := threshold_gap hd0 h72'
  have hden : 0 < (d : ℝ) - 6 * K := lt_trans (by positivity) hgap
  have hAC : A ⊆ C := by
    intro v hv
    have hv' : (d : ℝ) - 6 * K ≤ (xplus v : ℝ) := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hgap.trans_le hv'⟩
  have hAlower : (A.card : ℝ) * ((d : ℝ) - 6 * K) ≤ ∑ v, (xplus v : ℝ) := by
    calc
      _ = ∑ _v ∈ A, ((d : ℝ) - 6 * K) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ A, (xplus v : ℝ) :=
        Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v, (xplus v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hA : (A.card : ℝ) ≤ (d : ℝ) * k / ((d : ℝ) - 6 * K) := by
    apply (le_div_iff₀ hden).mpr
    exact hAlower.trans (by exact_mod_cast hplus)
  let rest : V → ℝ := fun v => if v ∈ A then 0 else (xplus v : ℝ)
  have hrest : (∑ v, rest v) ≤ 6 * (K : ℝ) * Fintype.card V :=
    residual_plus_le xplus xminus htotal hside
  have hBlower : (B.card : ℝ) * ((d : ℝ) / 8) ≤ ∑ v, rest v := by
    calc
      _ = ∑ _v ∈ B, ((d : ℝ) / 8) := by simp
      _ ≤ ∑ v ∈ B, rest v := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hvC, hvA⟩ := Finset.mem_sdiff.mp hv
        have hv' : (d : ℝ) / 8 < (xplus v : ℝ) := (Finset.mem_filter.mp hvC).2
        simpa only [rest, ite_eq_right hvA] using hv'.le
      _ ≤ ∑ v, rest v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _ _
        dsimp only [rest]
        split_ifs <;> positivity
  have hB : (B.card : ℝ) ≤ 48 * (K : ℝ) * Fintype.card V / d := by
    apply (le_div_iff₀ hd0).mpr
    nlinarith
  have hcard : (C.card : ℝ) = (A.card : ℝ) + B.card := by
    have hh := Finset.card_sdiff_add_card_eq_card hAC
    dsimp only [B]
    exact_mod_cast hh.symm.trans (Nat.add_comm _ _)
  change (C.card : ℝ) ≤ _
  rw [hcard]
  exact add_le_add hA hB

theorem cover_fraction_bound {d K k n : ℝ} (hd : 0 < d) (hK : 0 ≤ K)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) (h12 : 12 * K ≤ d) :
    d * k / (d - 6 * K) + 48 * K * n / d ≤ k + 60 * K * n / d := by
  have hn : 0 ≤ n := hk0.trans hkn
  have hden : 0 < d - 6 * K := by linarith
  have hmult := mul_le_mul_of_nonneg_left hkn (show 0 ≤ 6 * K * d by positivity)
  have hslack := mul_nonneg (show 0 ≤ 6 * K * n by positivity) (sub_nonneg.mpr h12)
  have hfrac : 6 * K * k / (d - 6 * K) ≤ 12 * K * n / d := by
    apply (div_le_div_iff₀ hden hd).mpr
    nlinarith
  have hid : d * k / (d - 6 * K) = k + 6 * K * k / (d - 6 * K) := by
    field_simp [hden.ne']; ring
  rw [hid]
  have hsplit : 60 * K * n / d = 12 * K * n / d + 48 * K * n / d := by ring
  rw [hsplit]
  linarith

theorem thresholdCover_card_le {d K k : ℕ} {ρ : ℝ} (xplus xminus : V → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d) (hk : k ≤ Fintype.card V)
    (hρ : 0 < ρ) (h120 : 120 * (K : ℝ) / ρ ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤ (k : ℝ) + ρ * Fintype.card V := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  calc
    _ ≤ (d : ℝ) * k / ((d : ℝ) - 6 * K) + 48 * (K : ℝ) * Fintype.card V / d :=
      thresholdCover_card_le_fractions xplus xminus hd h72 hplus htotal hside
    _ ≤ (k : ℝ) + 60 * (K : ℝ) * Fintype.card V / d :=
      cover_fraction_bound hd0 (Nat.cast_nonneg K) (Nat.cast_nonneg k)
        (by exact_mod_cast hk) (by linarith)
    _ ≤ (k : ℝ) + ρ * Fintype.card V :=
      add_le_add (le_refl (k : ℝ)) (sixty_loss_div_le hρ hd0 (Nat.cast_nonneg K)
        (Nat.cast_nonneg _) h120)

theorem thresholdCover_card_le_graph (G : GraphInput) {d K k : ℕ} {ρ : ℝ}
    (xplus xminus : G.Vertex → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d) (hk : k ≤ G.n)
    (hρ : 0 < ρ) (h120 : 120 * (K : ℝ) / ρ ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * G.n)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤ (k : ℝ) + ρ * G.n := by
  simpa only [Fintype.card_fin] using
    thresholdCover_card_le xplus xminus hd h72
      (by simpa only [Fintype.card_fin] using hk) hρ h120 hplus
      (by simpa only [Fintype.card_fin] using htotal) hside

end BinPackingGap

end

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

namespace BinPackingGap

namespace UniformTree

theorem mem_leaves_iff_length_eq_height (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) : w ∈ T.leaves ↔ w.length = T.height := by
  constructor
  · exact T.length_leaf w
  · intro hlen
    obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp hw
    have heq : w = l := h.eq_of_length (hlen.trans (T.length_leaf l hl).symm)
    simpa only [heq] using hl

theorem leaf_iff_depth_eq_height {T : UniformTree} (v : T.Node) :
    leaf v ↔ depth v = T.height :=
  T.mem_leaves_iff_length_eq_height v.property

theorem ancestorAt_ancestor {T : UniformTree} (v : T.Node) (k : ℕ) :
    ancestor (ancestorAt v k) v := List.take_prefix k v.val

theorem depth_ancestorAt {T : UniformTree} (v : T.Node) {k : ℕ}
    (hk : k ≤ depth v) : depth (ancestorAt v k) = k := by
  exact List.length_take_of_le hk

end UniformTree

end BinPackingGap

namespace BinPackingGap.TreeGeometry

open _root_.OAI.BinPackingGap.Geometry UniformTree

theorem cell_subset_of_prefix (m R D : ℕ) (s : Side) {u v : List ℕ}
    (h : u.IsPrefix v) (hv : BoundedAddress D v) :
    cell m R D s v ⊆ cell m R D s u := by
  have hb := prefix_endpoints m R D s h hv
  intro x hx
  exact ⟨hb.1.trans hx.1, hx.2.trans hb.2⟩

theorem eq_of_short_intersections (m R D : ℕ) {ell L : ℕ}
    (hell : ell ≤ L) {s t : Side} {u v : List ℕ} {a b : ℚ}
    (hu : u.length = ell) (hv : v.length = ell)
    (hbu : BoundedAddress D u) (hbv : BoundedAddress D v)
    (hlen : b - a ≤ lambda m R D ell + delta m R D L)
    (hiu : (Set.Icc a b ∩ cell m R D s u).Nonempty)
    (hiv : (Set.Icc a b ∩ cell m R D t v).Nonempty) : (s, u) = (t, v) := by
  by_contra hne
  have hgap := same_depth_gap m R D ell hu hv hbu hbv hne
  obtain ⟨x, hx, hxu⟩ := hiu
  obtain ⟨y, hy, hyv⟩ := hiv
  have hshort := lambda_add_delta_lt_three m R D hell
  rcases hgap with hgap | hgap
  · linarith [hx.1, hx.2, hy.1, hy.2, hxu.1, hxu.2, hyv.1, hyv.2]
  · linarith [hx.1, hx.2, hy.1, hy.2, hxu.1, hxu.2, hyv.1, hyv.2]

theorem nodeCell_subset_of_ancestor (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) {u v : T.Node} (h : ancestor u v) :
    nodeCell m R D s v ⊆ nodeCell m R D s u :=
  cell_subset_of_prefix m R D s h (boundedAddress_node v hD)

theorem nodeCell_subset_root (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) (v : T.Node) :
    nodeCell m R D s v ⊆ Set.Icc (rootOffset s) (rootOffset s + 1) := by
  simpa [nodeCell, cell] using
    nodeCell_subset_of_ancestor m R D s hD (root_ancestor v)

theorem mem_ancestor_cell (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) (v : T.Node) (ell : ℕ) {x : ℚ}
    (hx : x ∈ nodeCell m R D s v) :
    x ∈ nodeCell m R D s (ancestorAt v ell) :=
  nodeCell_subset_of_ancestor m R D s hD (ancestorAt_ancestor v ell) hx

end BinPackingGap.TreeGeometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingSelections
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open scoped BigOperators

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem globalCopy_injective (e : D.Item ≃ I.Item) (s : GlobalSpecies D.graph) :
    Function.Injective (fun i : Fin (D.globalStock s) => e ⟨.«global», ⟨s, i⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hg := @sigma_mk_injective Role D.RoleCopies .«global» _ _ h
  exact @sigma_mk_injective (GlobalSpecies D.graph)
    (fun s => Fin (D.globalStock s)) s i j hg

@[simp] theorem globalResources_card (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) :
    (globalResources e s).card = D.globalStock s := by
  classical
  simp only [globalResources, Finset.card_image_of_injective _ (globalCopy_injective e s),
    Finset.card_univ, Fintype.card_fin]

theorem fundedTuples_subset_main (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) :
    fundedTuples p e s v ⊆ Coverage.mainTuplesAt p (subclass e) (label e) v := by
  classical
  exact Finset.filter_subset _ _

theorem sum_card_main_subsets_le_resources (p : Packing I b) (e : D.Item ≃ I.Item)
    (S : D.Vertex → Finset (p.TableBin (subclass e)))
    (hS : ∀ v, S v ⊆ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (r : Role) (resources : Finset I.Item)
    (hres : ∀ v t, t ∈ S v → p.itemAtRole (subclass e) t r ∈ resources) :
    (∑ v, (S v).card) ≤ resources.card := by
  classical
  have hdis : ∀ v ∈ (Finset.univ : Finset D.Vertex),
      ∀ w ∈ (Finset.univ : Finset D.Vertex), v ≠ w → Disjoint (S v) (S w) := by
    intro v _ w _ hvw
    exact (Coverage.mainTuplesAt_disjoint_label p (subclass e) (label e) hvw).mono
      (hS v) (hS w)
  calc
    (∑ v, (S v).card) = (Finset.univ.biUnion S).card :=
      (Finset.card_biUnion hdis).symm
    _ ≤ resources.card := by
      apply Coverage.card_le_role_resources p (subclass e) _ r resources
      intro t ht
      obtain ⟨v, _, htv⟩ := Finset.mem_biUnion.mp ht
      exact hres v t htv

theorem fundedTuples_sum_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) :
    (∑ v, (fundedTuples p e s v).card) ≤ D.globalStock s := by
  rw [← globalResources_card e s]
  apply sum_card_main_subsets_le_resources p e (fundedTuples p e s)
    (fundedTuples_subset_main p e s) .«global» (globalResources e s)
  intro v t ht
  exact ((mem_fundedTuples p e s v t).mp ht).2

theorem xplus_budget (p : Packing I b) (e : D.Item ≃ I.Item) :
    (∑ v, xplus p e v) ≤ D.d * D.k :=
  fundedTuples_sum_card_le p e (.up true)

theorem xminus_budget (p : Packing I b) (e : D.Item ≃ I.Item) :
    (∑ v, xminus p e v) ≤ D.d * (D.graph.n - D.k) :=
  fundedTuples_sum_card_le p e (.um true)

theorem total_budget (p : Packing I b) (e : D.Item ≃ I.Item) (hk : D.k ≤ D.graph.n) :
    (∑ v, (xplus p e v + xminus p e v)) ≤ D.d * D.graph.n := by
  rw [Finset.sum_add_distrib]
  calc
    _ ≤ D.d * D.k + D.d * (D.graph.n - D.k) :=
      Nat.add_le_add (xplus_budget p e) (xminus_budget p e)
    _ = D.d * D.graph.n := by
      have hsum : D.k + (D.graph.n - D.k) = D.graph.n := by omega
      rw [← Nat.mul_add, hsum]

theorem localDepthCopy_injective (e : D.Item ≃ I.Item) (v : D.Vertex) (ell : D.Depth) :
    Function.Injective (fun i : Fin (D.quota ell.val) =>
      e ⟨.«local», ⟨v, Sum.inl (Sum.inl ⟨ell, i⟩)⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hl := @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  have hv := @sigma_mk_injective D.Vertex D.LocalAt v _ _ hl
  have hp : (⟨ell, i⟩ : D.PositiveLocal) = ⟨ell, j⟩ :=
    Sum.inl.inj (Sum.inl.inj hv)
  exact @sigma_mk_injective D.Depth (fun ell => Fin (D.quota ell.val)) ell i j hp

@[simp] theorem localDepthResources_card (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) :
    (localDepthResources e v ell).card = D.quota ell.val := by
  classical
  simp only [localDepthResources,
    Finset.card_image_of_injective _ (localDepthCopy_injective e v ell),
    Finset.card_univ, Fintype.card_fin]

theorem card_le_localDepth_stock (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) (S : Finset (p.TableBin (subclass e)))
    (hres : ∀ t ∈ S,
      p.itemAtRole (subclass e) t .«local» ∈ localDepthResources e v ell) :
    S.card ≤ D.quota ell.val := by
  rw [← localDepthResources_card e v ell]
  exact Coverage.card_le_role_resources p (subclass e) S .«local» _ hres

end PackingCounts
end BinPackingGap

end

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

theorem localCopy_eq_of_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hpos : p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v) :
    ∃ i : D.PositiveLocal, localCopy p e t = ⟨v, Sum.inl (Sum.inl i)⟩ := by
  obtain ⟨i, hi⟩ := (mem_positiveLocalResources e v _).mp hpos
  refine ⟨i, ?_⟩
  rw [← roleCopy_item p e t .«local»] at hi
  have h := e.injective hi
  have h' : (⟨v, Sum.inl (Sum.inl i)⟩ : Σ w : D.Vertex, D.LocalAt w) =
      localCopy p e t := by
    exact @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  exact h'.symm

theorem selected_depth_mem (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) :
    tupleLocalDepth p e t ∈ Finset.Icc 1 D.L := by
  obtain ⟨i, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  have hd : tupleLocalDepth p e t = i.1.val := by
    unfold tupleLocalDepth
    rw [hi]
    rfl
  rw [hd]
  exact i.1.property

theorem selected_localDepth_resource (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hell : tupleLocalDepth p e t = ell.val) :
    p.itemAtRole (subclass e) t .«local» ∈ localDepthResources e v ell := by
  classical
  obtain ⟨⟨depth, i⟩, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  have hd : tupleLocalDepth p e t = depth.val := by
    unfold tupleLocalDepth
    rw [hi]
    rfl
  have hdepth : depth = ell := Subtype.ext (hd.symm.trans hell)
  subst depth
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [← roleCopy_item p e t .«local»]
  exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩) hi.symm

theorem zeroPositiveTuples_depth_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) :
    ((zeroPositiveTuples p e v).filter (fun t => tupleLocalDepth p e t = ell.val)).card ≤
      D.quota ell.val := by
  classical
  apply card_le_localDepth_stock p e v ell
  intro t ht
  obtain ⟨ht, he⟩ := Finset.mem_filter.mp ht
  exact selected_localDepth_resource p e v ell t ht he

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

theorem tupleFinish_le_baseline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : tupleFinish p e t ≤ tupleBaseline p e t :=
  completion_le_baseline _ _ _ _ _ (tupleGlobalLength_nonneg p e t)
    (tupleLocalLength_nonneg p e t) (Geometry.delta_nonneg _ _ _ _)

theorem selected_localLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleLocalLength p e t =
      Geometry.lambda D.graph.edges.length D.R D.geometryBound (tupleLocalDepth p e t) := by
  obtain ⟨i, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  unfold tupleLocalLength tupleLocalDepth
  rw [hi]
  rfl

theorem selected_interval_length (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleBaseline p e t - tupleFinish p e t ≤
      Geometry.lambda D.graph.edges.length D.R D.geometryBound (tupleLocalDepth p e t) +
        Geometry.delta D.graph.edges.length D.R D.geometryBound D.L := by
  have hu := ((mem_zeroPositiveTuples p e v t).mp ht).2.1
  unfold tupleFinish
  rw [tupleGlobalLength_eq_of_unit_false p e t hu, selected_localLength p e v t ht]
  exact completion_zero_global_length_le _ _ _ _ (Geometry.delta_nonneg _ _ _ _)

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

theorem rowBaseline_le_one_of_not_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r ≠ .tm) : D.rowBaseline r ≤ 1 := by
  rcases r with t | ⟨short, j⟩
  · rcases t with ⟨node, i⟩ | ⟨node, i⟩ | i
    · have h := D.node_right_in_root node .plus D.plus_branch_le_geometryBound
      simpa only [rowBaseline, treeBaseline, TreeGeometry.rootOffset, zero_add] using h.2
    · exact (hclass rfl).elim
    · exact le_rfl
  · exact (Geometry.job_baseline_lt_one _ _ _).le

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

theorem row_zero_resources_empty {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = false) :
    completionInterval (D.rowBaseline r) (D.rowShort r) 0 0
      (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) = ∅ := by
  rw [hshort]
  exact completionInterval_long_zero_lengths _ _

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

end BinPackingGap.InventoryData

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

theorem actual_deadline_deficit_bound
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) (K : ℕ)
    (finish : p.TableBin (PackingCounts.subclass e) → ℚ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hle : ∀ t ∈ Coverage.mainTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      finish t ≤ rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x))
    (hfeasible : ∀ t ∈ Coverage.mainTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      finish t ≤ anchorDeadline e (p.itemAtRole (PackingCounts.subclass e) t .anchor)) :
    (Finset.univ.filter fun z : D.MBase v => D.deadline z ≤ a).card ≤
      (originalBaselinePrefix D v a).card +
      (Coverage.coveringTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
        (rowBaseline e) finish a).card + 6 * K := by
  classical
  have hbase := actual_displaced_baseline_prefix_le p e v a ∅ K hbad horder
    (Finset.empty_subset _) (by simp) (by simp)
  simp only [Finset.card_empty, Nat.add_zero] at hbase
  have hdeadline := Coverage.deadline_prefix_le_completion_add_loss p
    (PackingCounts.subclass e) (PackingCounts.label e) v (anchorDeadline e) finish a K
    hbad hfeasible
  rw [deadlinePrefix_card] at hdeadline
  have hsplit := Coverage.completion_prefix_decomposition p (PackingCounts.subclass e)
    (PackingCounts.label e) v (rowBaseline e) finish hle a
  omega

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
attribute [-instance] _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor
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

end InventoryCoverage

namespace InventoryData

variable (D : InventoryData)

theorem test_coverage {b c : ℕ}
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (v : D.Vertex) (t : D.TestAt v) (a : ℚ) (ha : a ∈ D.testInterval t) :
    D.d ≤ (PackingCounts.tupleCovering p D.itemEquiv v a).card + 6 * lossAllowance c := by
  classical
  have hbad := D.badAnchorsAt_card_le_oaiq082 hk p hb v
  have horder := PackingCounts.edge_selected_baseline_le p D.itemEquiv
    D.packingInstance_size_eq v
  have hle : ∀ u ∈ Coverage.mainTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v,
      PackingCounts.tupleFinish p D.itemEquiv u ≤
        InventoryCoverage.rowBaseline D.itemEquiv (p.itemAtRole (PackingCounts.subclass D.itemEquiv) u .x) := by
    intro u _
    simpa only [InventoryCoverage.rowBaseline_selected, PackingCounts.tupleBaseline] using
      PackingCounts.tupleFinish_le_baseline p D.itemEquiv u
  have hfeasible := PackingCounts.main_completion_le_selected_deadline p D.itemEquiv
    D.packingInstance_size_eq v
  have hdeficit := InventoryCoverage.actual_deadline_deficit_bound p D.itemEquiv v a
    (lossAllowance c) (PackingCounts.tupleFinish p D.itemEquiv) hbad horder hle hfeasible
  rw [D.deadline_prefix_at_test hplusheight hminusheight hL v t a ha,
    InventoryCoverage.coveringTuplesAt_eq] at hdeficit
  change (InventoryCoverage.originalBaselinePrefix D v a).card + D.d ≤
    (InventoryCoverage.originalBaselinePrefix D v a).card +
      (PackingCounts.tupleCovering p D.itemEquiv v a).card + 6 * lossAllowance c at hdeficit
  omega

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_ExtractedCover
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.SideChoice

open UniformTree

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem card_le_of_unique_hit [DecidableEq α] [DecidableEq β]
    (tuples : Finset α) (nodes : Finset β)
    (hits : α → β → Prop)
    (hcover : ∀ v ∈ nodes, ∃ t ∈ tuples, hits t v)
    (hunique : ∀ t ∈ tuples, ∀ v w, hits t v → hits t w → v = w) :
    nodes.card ≤ tuples.card := by
  classical
  let f : nodes → tuples := fun v =>
    ⟨Classical.choose (hcover v.val v.property),
      (Classical.choose_spec (hcover v.val v.property)).1⟩
  have hf : ∀ v : nodes, hits (f v).val v.val := fun v =>
    (Classical.choose_spec (hcover v.val v.property)).2
  apply Finset.card_le_card_of_injective (f := f)
  intro v w hvw
  apply Subtype.ext
  have ht : (f v).val = (f w).val := congrArg Subtype.val hvw
  apply hunique (f v).val (f v).property v.val w.val (hf v)
  rw [ht]
  exact hf w

variable {d : ℕ} (T : CompetingTrees d)

theorem roots_not_marked (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t) :
    T.plus.root ∉ marksPlus T selected hits ∧
      T.minus.root ∉ marksMinus T selected hits := by
  constructor
  · intro hroot
    obtain ⟨t, ht, hhit⟩ := (mem_marksPlus T selected hits _).mp hroot
    have hh : 0 = level t := hdepth t ht (.inl T.plus.root) hhit
    have hp := hpositive t ht
    omega
  · intro hroot
    obtain ⟨t, ht, hhit⟩ := (mem_marksMinus T selected hits _).mp hroot
    have hh : 0 = level t := hdepth t ht (.inr T.minus.root) hhit
    have hp := hpositive t ht
    omega

theorem marked_level_card_le (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (ℓ : ℕ) :
    ((marksPlus T selected hits).filter fun v => depth v = ℓ).card +
      ((marksMinus T selected hits).filter fun v => depth v = ℓ).card ≤
      (selected.filter fun t => level t = ℓ).card := by
  classical
  rw [← Finset.card_disjSum]
  apply card_le_of_unique_hit _ _ hits
  · intro v hv
    cases v with
    | inl v =>
      have hv' := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hv)
      obtain ⟨t, ht, hhit⟩ := (mem_marksPlus T selected hits v).mp hv'.1
      refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, hhit⟩
      have hh : depth v = level t := hdepth t ht (.inl v) hhit
      exact hh.symm.trans hv'.2
    | inr v =>
      have hv' := Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hv)
      obtain ⟨t, ht, hhit⟩ := (mem_marksMinus T selected hits v).mp hv'.1
      refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, hhit⟩
      have hh : depth v = level t := hdepth t ht (.inr v) hhit
      exact hh.symm.trans hv'.2
  · intro t ht v w hv hw
    exact hunique t (Finset.mem_filter.mp ht).1 v w hv hw

theorem exists_unhit_leaf (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ) :
    (∃ l : T.plus.Node, leaf l ∧
      ∀ t ∈ selected, ∀ v, hits t (.inl v) → ¬ ancestor v l) ∨
    (∃ l : T.minus.Node, leaf l ∧
      ∀ t ∈ selected, ∀ v, hits t (.inr v) → ¬ ancestor v l) := by
  have hroots := roots_not_marked T selected level hits hpositive hdepth
  have hquota : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      ((marksPlus T selected hits).filter fun v => depth v = ℓ).card +
        ((marksMinus T selected hits).filter fun v => depth v = ℓ).card ≤ T.quota ℓ := by
    intro ℓ hlo hhi
    exact (marked_level_card_le T selected level hits hdepth hunique ℓ).trans
      (hstock ℓ hlo hhi)
  rcases T.shared_obstruction (marksPlus T selected hits) (marksMinus T selected hits)
    hroots.1 hroots.2 hquota with ⟨l, hl, havoid⟩ | ⟨l, hl, havoid⟩
  · left
    refine ⟨l, hl, ?_⟩
    intro t ht v hhit
    exact havoid v ((mem_marksPlus T selected hits v).mpr ⟨t, ht, hhit⟩)
  · right
    refine ⟨l, hl, ?_⟩
    intro t ht v hhit
    exact havoid v ((mem_marksMinus T selected hits v).mpr ⟨t, ht, hhit⟩)

theorem exists_leaf_coverage_le_funded (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (fundPlus fundMinus : Finset α)
    (coverPlus : T.plus.Node → Finset α) (coverMinus : T.minus.Node → Finset α)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ)
    (hcoverPlus : ∀ l, leaf l → ∀ t ∈ coverPlus l,
      t ∈ fundPlus ∨ t ∈ selected ∧ ∃ v, hits t (.inl v) ∧ ancestor v l)
    (hcoverMinus : ∀ l, leaf l → ∀ t ∈ coverMinus l,
      t ∈ fundMinus ∨ t ∈ selected ∧ ∃ v, hits t (.inr v) ∧ ancestor v l) :
    (∃ l : T.plus.Node, leaf l ∧ (coverPlus l).card ≤ fundPlus.card) ∨
    (∃ l : T.minus.Node, leaf l ∧ (coverMinus l).card ≤ fundMinus.card) := by
  rcases exists_unhit_leaf T selected level hits hpositive hdepth hunique hstock with
    ⟨l, hl, havoid⟩ | ⟨l, hl, havoid⟩
  · left
    refine ⟨l, hl, Finset.card_le_card ?_⟩
    intro t ht
    rcases hcoverPlus l hl t ht with hfund | ⟨hselected, v, hhit, hancestor⟩
    · exact hfund
    · exact (havoid t hselected v hhit hancestor).elim
  · right
    refine ⟨l, hl, Finset.card_le_card ?_⟩
    intro t ht
    rcases hcoverMinus l hl t ht with hfund | ⟨hselected, v, hhit, hancestor⟩
    · exact hfund
    · exact (havoid t hselected v hhit hancestor).elim

theorem side_choice (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (fundPlus fundMinus : Finset α)
    (coverPlus : T.plus.Node → Finset α) (coverMinus : T.minus.Node → Finset α)
    (K : ℕ)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ)
    (hcoverPlus : ∀ l, leaf l → ∀ t ∈ coverPlus l,
      t ∈ fundPlus ∨ t ∈ selected ∧ ∃ v, hits t (.inl v) ∧ ancestor v l)
    (hcoverMinus : ∀ l, leaf l → ∀ t ∈ coverMinus l,
      t ∈ fundMinus ∨ t ∈ selected ∧ ∃ v, hits t (.inr v) ∧ ancestor v l)
    (hlowerPlus : ∀ l, leaf l → d ≤ (coverPlus l).card + 6 * K)
    (hlowerMinus : ∀ l, leaf l → d ≤ (coverMinus l).card + 6 * K) :
    d ≤ fundPlus.card + 6 * K ∨ d ≤ fundMinus.card + 6 * K := by
  rcases exists_leaf_coverage_le_funded T selected level hits fundPlus fundMinus
    coverPlus coverMinus hpositive hdepth hunique hstock hcoverPlus hcoverMinus with
    ⟨l, hl, hle⟩ | ⟨l, hl, hle⟩
  · exact Or.inl ((hlowerPlus l hl).trans (Nat.add_le_add_right hle _))
  · exact Or.inr ((hlowerMinus l hl).trans (Nat.add_le_add_right hle _))

end BinPackingGap.SideChoice

namespace BinPackingGap

section

theorem reductionInventory_height_pos (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    0 < (reductionInventory c ρ G k).L := (reductionTrees c ρ).height_pos

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

private theorem selected_inventory_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemSubclass ⟨r, roleCopy p e t r⟩ =
      patternSubclass (p.tablePattern (subclass e) t) r := by
  have h := p.itemAtRole_subclass (subclass e) t r
  rw [← roleCopy_item p e t r] at h
  simpa only [subclass, Function.comp_apply, Equiv.symm_apply_apply] using h

private theorem selected_row_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    D.rowSubclass (rowCopy p e t).2 =
      patternSubclass (p.tablePattern (subclass e) t) .x := by
  have h := selected_inventory_subclass p e t .x
  change D.itemSubclass ⟨.x, rowCopy p e t⟩ = _ at h
  rcases hc : rowCopy p e t with ⟨v, r⟩
  simpa only [hc, InventoryData.itemSubclass] using h

private theorem unit_global_species (u : D.GlobalCopy) (hu : D.globalUnit u = true) :
    u.1 = .up true ∨ u.1 = .um true := by
  rcases u with ⟨s, i⟩
  cases s with
  | up one => cases one <;> simp_all [InventoryData.globalUnit]
  | um one => cases one <;> simp_all [InventoryData.globalUnit]
  | edge edge permit => simp [InventoryData.globalUnit] at hu

private theorem selected_row_tm_of_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {one : Bool}
    (hs : (globalCopy p e t).1 = .um one) :
    D.rowSubclass (rowCopy p e t).2 = .tm := by
  have hg := selected_inventory_subclass p e t .«global»
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .um := by
    rcases hc : globalCopy p e t with ⟨s, i⟩
    have hs' : s = .um one := by simpa only [hc] using hs
    subst s
    rfl
  rw [hclass] at hg
  have hx := selected_row_subclass p e t
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

private theorem selected_row_not_tm_of_up (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {one : Bool}
    (hs : (globalCopy p e t).1 = .up one) :
    D.rowSubclass (rowCopy p e t).2 ≠ .tm := by
  have hg := selected_inventory_subclass p e t .«global»
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .up := by
    rcases hc : globalCopy p e t with ⟨s, i⟩
    have hs' : s = .up one := by simpa only [hc] using hs
    subst s
    rfl
  rw [hclass] at hg
  have hx := selected_row_subclass p e t
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

private theorem selected_global_resource (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    p.itemAtRole (subclass e) t .«global» ∈
      globalResources e (globalCopy p e t).1 := by
  apply (mem_globalResources e _ _).mpr
  refine ⟨(globalCopy p e t).2, ?_⟩
  exact roleCopy_item p e t .«global»

private theorem funded_of_species (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    {s : GlobalSpecies D.graph} (hs : (globalCopy p e t).1 = s) :
    t ∈ fundedTuples p e s v := by
  apply (mem_fundedTuples p e s v t).mpr
  refine ⟨ht, ?_⟩
  have hr := selected_global_resource p e t
  rwa [hs] at hr

theorem covering_plus_unit_funded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (leaf : D.PlusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = true)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    t ∈ fundedTuples p e (.up true) v := by
  rcases unit_global_species (globalCopy p e t) hu with hup | hum
  · exact funded_of_species p e v t ht hup
  · have hrow := selected_row_tm_of_um p e t hum
    have hfinish : 1 < tupleFinish p e t :=
      D.minus_row_completion_gt_one (rowCopy p e t).2 (globalCopy p e t)
        (localCopy p e t).2 hrow
    have hroot := TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R
      D.geometryBound .plus D.plus_branch_le_geometryBound leaf.val ha
    have ha1 : a ≤ 1 := by
      simpa only [TreeGeometry.rootOffset, zero_add] using hroot.2
    exact False.elim (by linarith only [hfinish, ha1, hc.1])

theorem covering_minus_unit_funded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (leaf : D.MinusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = true)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    t ∈ fundedTuples p e (.um true) v := by
  rcases unit_global_species (globalCopy p e t) hu with hup | hum
  · have hrow := selected_row_not_tm_of_up p e t hup
    have hbase : tupleBaseline p e t ≤ 1 :=
      D.rowBaseline_le_one_of_not_tm (rowCopy p e t).2 hrow
    have hroot := TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R
      D.geometryBound .minus D.minus_branch_le_geometryBound leaf.val ha
    have ha4 : 4 ≤ a := hroot.1
    exact False.elim (by linarith only [hbase, ha4, hc.2])
  · exact funded_of_species p e v t ht hum

theorem zero_lengths_cover_jobCell (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {a : ℚ}
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ j : D.JobCopy (rowCopy p e t).1,
      a ∈ D.testCell (.inr (.inr j.1) : D.TestAt (rowCopy p e t).1) := by
  have hg := tupleGlobalLength_eq_of_unit_false p e t hu
  have hmem : a ∈ completionInterval (tupleBaseline p e t) (tupleShort p e t) 0 0
      (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
    change completion (tupleBaseline p e t) (tupleShort p e t) 0 0 _ ≤ a ∧
      a < tupleBaseline p e t
    simpa only [tupleFinish, hg, hl] using hc
  change a ∈ completionInterval (D.rowBaseline (rowCopy p e t).2)
    (D.rowShort (rowCopy p e t).2) 0 0
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) at hmem
  by_cases hs : D.rowShort (rowCopy p e t).2 = true
  · obtain ⟨j, _, _, hj⟩ := D.row_zero_resources_job (rowCopy p e t).2 hs
    rw [hj] at hmem
    refine ⟨j, ?_⟩
    change a ∈ Geometry.closedJobCell D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)
    exact ⟨hmem.1, hmem.2.le⟩
  · have hsfalse : D.rowShort (rowCopy p e t).2 = false := by
      cases hh : D.rowShort (rowCopy p e t).2 <;> simp_all
    rw [D.row_zero_resources_empty (rowCopy p e t).2 hsfalse] at hmem
    cases hmem

theorem zero_lengths_not_cover_plus_leaf (p : Packing I b) (e : D.Item ≃ I.Item)
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (t : p.TableBin (subclass e)) (leaf : D.PlusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0) :
    ¬ (tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) := by
  intro hc
  obtain ⟨j, hj⟩ := zero_lengths_cover_jobCell p e t hu hl hc
  have hleaf : a ∈ D.testCell (.inl leaf : D.TestAt (rowCopy p e t).1) := ha
  have hdis := D.testCell_disjoint hplusheight hminusheight hL
    (show (.inl leaf : D.TestAt (rowCopy p e t).1) ≠ .inr (.inr j.1) by
      intro h; cases h)
  exact Set.disjoint_left.mp hdis hleaf hj

theorem zero_lengths_not_cover_minus_leaf (p : Packing I b) (e : D.Item ≃ I.Item)
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (t : p.TableBin (subclass e)) (leaf : D.MinusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0) :
    ¬ (tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) := by
  intro hc
  obtain ⟨j, hj⟩ := zero_lengths_cover_jobCell p e t hu hl hc
  have hleaf : a ∈ D.testCell (.inr (.inl leaf) : D.TestAt (rowCopy p e t).1) := ha
  have hdis := D.testCell_disjoint hplusheight hminusheight hL
    (show (.inr (.inl leaf) : D.TestAt (rowCopy p e t).1) ≠ .inr (.inr j.1) by
      intro h; cases h)
  exact Set.disjoint_left.mp hdis hleaf hj

end PackingCounts

open UniformTree

namespace InventoryData

variable (D : InventoryData)

theorem plusPoint_mem_Ico (v : D.plus.Node) :
    D.plusPoint v ∈ Set.Ico
      (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus v.val)
      (TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus v.val) := by
  have h := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound .plus v.val
  dsimp only [plusPoint, Set.mem_Ico]
  constructor <;> linarith

theorem minusPoint_mem_Ico (v : D.minus.Node) :
    D.minusPoint v ∈ Set.Ico
      (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus v.val)
      (TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus v.val) := by
  have h := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound .minus v.val
  dsimp only [minusPoint, Set.mem_Ico]
  constructor <;> linarith

theorem plusPoint_mem_cell (v : D.plus.Node) :
    D.plusPoint v ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus v :=
  ⟨(D.plusPoint_mem_Ico v).1, (D.plusPoint_mem_Ico v).2.le⟩

theorem minusPoint_mem_cell (v : D.minus.Node) :
    D.minusPoint v ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus v :=
  ⟨(D.minusPoint_mem_Ico v).1, (D.minusPoint_mem_Ico v).2.le⟩

theorem taggedAddress_injective : Function.Injective D.taggedAddress := by
  intro u v h
  cases u with
  | inl u =>
    cases v with
    | inl v => exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd h))
    | inr v => have hs := congrArg Prod.fst h; cases hs
  | inr u =>
    cases v with
    | inl v => have hs := congrArg Prod.fst h; cases hs
    | inr v => exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd h))

theorem taggedAddress_bounded (v : D.plus.Node ⊕ D.minus.Node) :
    TreeGeometry.BoundedAddress D.geometryBound (D.taggedAddress v).2 := by
  cases v with
  | inl v => exact TreeGeometry.boundedAddress_node v D.plus_branch_le_geometryBound
  | inr v => exact TreeGeometry.boundedAddress_node v D.minus_branch_le_geometryBound

end InventoryData

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem selected_hits_unique (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v)
    (u w : D.plus.Node ⊕ D.minus.Node)
    (hu : tupleHits p e t u) (hw : tupleHits p e t w) : u = w := by
  apply D.taggedAddress_injective
  exact TreeGeometry.eq_of_short_intersections D.graph.edges.length D.R D.geometryBound
    (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
    hu.1 hw.1 (D.taggedAddress_bounded u) (D.taggedAddress_bounded w)
    (selected_interval_length p e v t ht) hu.2 hw.2

theorem main_local_nonzero_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (hlocal : tupleLocalLength p e t ≠ 0) :
    p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v := by
  have hlabel := good_local_vertex p e v t
    (Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v ht)
  cases hcopy : localCopy p e t with
  | mk w l =>
    have hwv : w = v := by simpa only [hcopy] using hlabel
    subst w
    rcases l with ((i | z) | j)
    · apply (mem_positiveLocalResources e v _).mpr
      refine ⟨i, ?_⟩
      rw [← roleCopy_item p e t .«local»]
      exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩)
        hcopy.symm
    · exact (hlocal (congrArg
        (fun x : (Σ w : D.Vertex, D.LocalAt w) => D.localLength x.2) hcopy)).elim
    · exact (hlocal (congrArg
        (fun x : (Σ w : D.Vertex, D.LocalAt w) => D.localLength x.2) hcopy)).elim

theorem selected_hits_plus_ancestor (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hheight : D.plus.height = D.L)
    (l : D.plus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus l)
    (hcover : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ u : D.plus.Node, tupleHits p e t (.inl u) ∧ ancestor u l := by
  let ell := tupleLocalDepth p e t
  have hell : ell ≤ depth l := by
    rw [(leaf_iff_depth_eq_height l).mp hl, hheight]
    exact (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
  refine ⟨ancestorAt l ell, ⟨depth_ancestorAt l hell, ?_⟩, ancestorAt_ancestor l ell⟩
  refine ⟨a, ⟨hcover.1, hcover.2.le⟩, ?_⟩
  exact TreeGeometry.mem_ancestor_cell D.graph.edges.length D.R D.geometryBound .plus
    D.plus_branch_le_geometryBound l ell ha

theorem selected_hits_minus_ancestor (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hheight : D.minus.height = D.L)
    (l : D.minus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus l)
    (hcover : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ u : D.minus.Node, tupleHits p e t (.inr u) ∧ ancestor u l := by
  let ell := tupleLocalDepth p e t
  have hell : ell ≤ depth l := by
    rw [(leaf_iff_depth_eq_height l).mp hl, hheight]
    exact (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
  refine ⟨ancestorAt l ell, ⟨depth_ancestorAt l hell, ?_⟩, ancestorAt_ancestor l ell⟩
  refine ⟨a, ⟨hcover.1, hcover.2.le⟩, ?_⟩
  exact TreeGeometry.mem_ancestor_cell D.graph.edges.length D.R D.geometryBound .minus
    D.minus_branch_le_geometryBound l ell ha

theorem covering_plus_classification (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (l : D.plus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus l)
    (ht : t ∈ tupleCovering p e v a) :
    t ∈ fundedTuples p e (.up true) v ∨
      t ∈ zeroPositiveTuples p e v ∧
        ∃ u : D.plus.Node, tupleHits p e t (.inl u) ∧ ancestor u l := by
  obtain ⟨hmain, hcover⟩ := (mem_tupleCovering p e v a t).mp ht
  cases hu : D.globalUnit (globalCopy p e t) with
  | false =>
    have hlocal : tupleLocalLength p e t ≠ 0 := by
      intro hz
      exact zero_lengths_not_cover_plus_leaf p e hplusheight hminusheight hL t
        ⟨l, hl⟩ ha hu hz hcover
    have hselected : t ∈ zeroPositiveTuples p e v :=
      (mem_zeroPositiveTuples p e v t).mpr
        ⟨hmain, hu, main_local_nonzero_positive p e v t hmain hlocal⟩
    exact Or.inr ⟨hselected,
      selected_hits_plus_ancestor p e v t hselected hplusheight l hl ha hcover⟩
  | true =>
    exact Or.inl (covering_plus_unit_funded p e v t hmain ⟨l, hl⟩ ha hu hcover)

theorem covering_minus_classification (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (l : D.minus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus l)
    (ht : t ∈ tupleCovering p e v a) :
    t ∈ fundedTuples p e (.um true) v ∨
      t ∈ zeroPositiveTuples p e v ∧
        ∃ u : D.minus.Node, tupleHits p e t (.inr u) ∧ ancestor u l := by
  obtain ⟨hmain, hcover⟩ := (mem_tupleCovering p e v a t).mp ht
  cases hu : D.globalUnit (globalCopy p e t) with
  | false =>
    have hlocal : tupleLocalLength p e t ≠ 0 := by
      intro hz
      exact zero_lengths_not_cover_minus_leaf p e hplusheight hminusheight hL t
        ⟨l, hl⟩ ha hu hz hcover
    have hselected : t ∈ zeroPositiveTuples p e v :=
      (mem_zeroPositiveTuples p e v t).mpr
        ⟨hmain, hu, main_local_nonzero_positive p e v t hmain hlocal⟩
    exact Or.inr ⟨hselected,
      selected_hits_minus_ancestor p e v t hselected hminusheight l hl ha hcover⟩
  | true =>
    exact Or.inl (covering_minus_unit_funded p e v t hmain ⟨l, hl⟩ ha hu hcover)

theorem side_choice_of_competingTrees (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) (p : Packing I b)
    (e : (InventoryData.ofCompetingTrees G T R k).Item ≃ I.Item)
    (v : G.Vertex) (K : ℕ)
    (hlowerPlus : ∀ l : T.plus.Node, leaf l →
      d ≤ (tupleCovering p e v ((InventoryData.ofCompetingTrees G T R k).plusPoint l)).card +
        6 * K)
    (hlowerMinus : ∀ l : T.minus.Node, leaf l →
      d ≤ (tupleCovering p e v ((InventoryData.ofCompetingTrees G T R k).minusPoint l)).card +
        6 * K) :
    d ≤ xplus p e v + 6 * K ∨ d ≤ xminus p e v + 6 * K := by
  classical
  let D := InventoryData.ofCompetingTrees G T R k
  change d ≤ (fundedTuples p e (.up true) v).card + 6 * K ∨
    d ≤ (fundedTuples p e (.um true) v).card + 6 * K
  apply SideChoice.side_choice T (zeroPositiveTuples p e v) (tupleLocalDepth p e)
    (tupleHits p e) (fundedTuples p e (.up true) v) (fundedTuples p e (.um true) v)
    (fun l => tupleCovering p e v (D.plusPoint l))
    (fun l => tupleCovering p e v (D.minusPoint l)) K
  · intro t ht
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).1
  · intro t _ w hhit
    cases w <;> exact hhit.1
  · intro t ht u w hu hw
    exact selected_hits_unique p e v t ht u w hu hw
  · intro ell hlo hhi
    exact zeroPositiveTuples_depth_card_le p e v
      ⟨ell, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩
  · intro l hl t ht
    exact covering_plus_classification p e v t T.plus_height T.minus_height
      (Nat.succ_le_of_lt T.height_pos) l hl (D.plusPoint_mem_cell l) ht
  · intro l hl t ht
    exact covering_minus_classification p e v t T.plus_height T.minus_height
      (Nat.succ_le_of_lt T.height_pos) l hl (D.minusPoint_mem_cell l) ht
  · exact hlowerPlus
  · exact hlowerMinus

theorem side_choice_of_test_coverage (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) (p : Packing I b)
    (e : (InventoryData.ofCompetingTrees G T R k).Item ≃ I.Item)
    (v : G.Vertex) (K : ℕ)
    (hcoverage : ∀ q : (InventoryData.ofCompetingTrees G T R k).TestAt v, ∀ a : ℚ,
      a ∈ (InventoryData.ofCompetingTrees G T R k).testInterval q →
        d ≤ (tupleCovering p e v a).card + 6 * K) :
    d ≤ xplus p e v + 6 * K ∨ d ≤ xminus p e v + 6 * K := by
  apply side_choice_of_competingTrees G T R k p e v K
  · intro l hl
    exact hcoverage (.inl ⟨l, hl⟩) _
      ((InventoryData.ofCompetingTrees G T R k).plusPoint_mem_Ico l)
  · intro l hl
    exact hcoverage (.inr (.inl ⟨l, hl⟩)) _
      ((InventoryData.ofCompetingTrees G T R k).minusPoint_mem_Ico l)

end PackingCounts

end

theorem reduction_side_choice (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) {b : ℕ} (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) (v : G.Vertex) :
    depthDemand c ρ ≤ PackingCounts.xplus p (reductionInventory c ρ G k).itemEquiv v +
      6 * lossAllowance c ∨
    depthDemand c ρ ≤ PackingCounts.xminus p (reductionInventory c ρ G k).itemEquiv v +
      6 * lossAllowance c := by
  let D := reductionInventory c ρ G k
  apply PackingCounts.side_choice_of_test_coverage G (reductionTrees c ρ)
    D.R k p D.itemEquiv v (lossAllowance c)
  intro q a ha
  exact D.test_coverage (reductionInventory_plus_height c ρ G k)
    (reductionInventory_minus_height c ρ G k)
    (Nat.succ_le_of_lt (reductionInventory_height_pos c ρ G k)) hk p hb v q a ha

theorem extractedCover_card_le_oaiq082_oai (c : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (G : GraphInput) (k : ℕ) (hk : k ≤ G.n) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    ((extractedCover c ρ G k p).card : ℝ) ≤ (k : ℝ) + ρ * G.n := by
  let D := reductionInventory c ρ G k
  apply thresholdCover_card_le_graph G
    (PackingCounts.xplus p D.itemEquiv) (PackingCounts.xminus p D.itemEquiv)
    (depthDemand_pos c ρ) (depthDemand_ge_72 c ρ) hk hρ (depthDemand_ge_120_div c ρ)
  · exact PackingCounts.xplus_budget p D.itemEquiv
  · exact PackingCounts.total_budget p D.itemEquiv hk
  · exact reduction_side_choice c ρ G k hk p hb

end BinPackingGap

end

end OAI
end

theorem solution : type_of% @OAI.BinPackingGap.extractedCover_card_le_oaiq082_oai := @OAI.BinPackingGap.extractedCover_card_le_oaiq082_oai
