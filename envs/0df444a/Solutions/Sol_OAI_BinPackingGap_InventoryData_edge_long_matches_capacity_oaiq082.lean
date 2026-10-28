-- Prove2me | solution 1 for OAI.BinPackingGap.InventoryData.edge_long_matches_capacity_oaiq082
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:03:01.158172+00:00
-- url     : https://prove2.me/submissions/5df3fa67-e6f8-4fa4-a185-04be4b1aeaf3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C021

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

theorem mem_own_bin (p : Packing I b) (i : I.Item) :
    i ∈ p.binItems (p.assignment i) := by simp

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

namespace IndividualConfiguration

variable {I : Instance}

theorem card_le_five (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (H : IndividualConfiguration I) : H.val.card ≤ 5 := by
  by_contra h
  have hcard : 6 ≤ H.val.card := by omega
  have hne : H.val.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hlarge i)
  have hsum : (H.val.card : ℚ) * (1 / 6) < ∑ i ∈ H.val, I.size i := by
    simpa using hstrict
  have hc : (6 : ℚ) ≤ H.val.card := by exact_mod_cast hcard
  have hcap := H.property
  linarith

end IndividualConfiguration

namespace Packing

theorem bin_card_le_five {I : Instance} {b : ℕ}
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) (p : Packing I b) (j : Fin b) :
    (p.binItems j).card ≤ 5 :=
  (p.configuration j).card_le_five hlarge

end Packing

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PrimaryLoss
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PrimaryLoss

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {N : ℕ}

theorem sum_fibers (f : ι → Fin N) (s : Finset (Fin N))
    {A : Type*} [AddCommMonoid A] (w : ι → A) :
    (∑ b ∈ s, ∑ i ∈ fiber f b, w i) = ∑ i ∈ itemsIn f s, w i := by
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ s f w

theorem card_itemsIn (f : ι → Fin N) (s : Finset (Fin N)) :
    (itemsIn f s).card = ∑ b ∈ s, (fiber f b).card := by
  exact (Finset.sum_card_fiberwise_eq_card_filter Finset.univ s f).symm

theorem sum_fiber_card (f : ι → Fin N) :
    ∑ b, (fiber f b).card = Fintype.card ι := by
  simpa [itemsIn] using (card_itemsIn f Finset.univ).symm

theorem sum_binPrimary (f : ι → Fin N) (p : ι → ℤ) :
    ∑ b, binPrimary f p b = ∑ i, p i := by
  simpa [itemsIn, binPrimary] using sum_fibers f Finset.univ p

theorem card_itemsIn_le (f : ι → Fin N)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (s : Finset (Fin N)) :
    (itemsIn f s).card ≤ 5 * s.card := by
  rw [card_itemsIn]
  calc
    (∑ b ∈ s, (fiber f b).card) ≤ ∑ _ ∈ s, 5 :=
      Finset.sum_le_sum fun b _ => hcap b
    _ = 5 * s.card := by simp [Nat.mul_comm]

theorem nonfullBins_card_le (f : ι → Fin N) (B c : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c) :
    (nonfullBins f).card ≤ 5 * c := by
  have hmass : ∑ b, (fiber f b).card = 5 * B := (sum_fiber_card f).trans hcard
  have hdef : (∑ b, (5 - (fiber f b).card)) = 5 * N - 5 * B := by
    rw [Finset.sum_tsub_distrib _ (fun b _ => hcap b), hmass]
    simp [Nat.mul_comm]
  calc
    (nonfullBins f).card = ∑ _ ∈ nonfullBins f, 1 := by simp
    _ ≤ ∑ b ∈ nonfullBins f, (5 - (fiber f b).card) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb' : (fiber f b).card < 5 := (Finset.mem_filter.mp hb).2
      omega
    _ ≤ ∑ b : Fin N, (5 - (fiber f b).card) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ 5 * c := by rw [hdef]; omega

theorem nonfullItems_card_le (f : ι → Fin N) (B c : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c) :
    (nonfullItems f).card ≤ 25 * c := by
  have hi := card_itemsIn_le f hcap (nonfullBins f)
  have hb := nonfullBins_card_le f B c hcard hcap hN
  change (itemsIn f (nonfullBins f)).card ≤ 25 * c
  omega

theorem full_nonfull_disjoint (f : ι → Fin N) :
    Disjoint (nonfullBins f) (fullBins f) := by
  apply Finset.disjoint_left.mpr
  intro b hn hf
  have hn' := (Finset.mem_filter.mp hn).2
  have hf' := (Finset.mem_filter.mp hf).2
  omega

theorem full_nonfull_union (f : ι → Fin N)
    (hcap : ∀ b, (fiber f b).card ≤ 5) :
    nonfullBins f ∪ fullBins f = Finset.univ := by
  ext b
  simp only [Finset.mem_union, nonfullBins, fullBins, Finset.mem_filter,
    Finset.mem_univ, true_and, iff_true]
  have := hcap b
  omega

theorem primary_conservation (f : ι → Fin N) (p : ι → ℤ)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (htotal : ∑ i, p i = 0) :
    (∑ b ∈ nonfullBins f, binPrimary f p b) +
      (∑ b ∈ fullBins f, binPrimary f p b) = 0 := by
  rw [← Finset.sum_union (full_nonfull_disjoint f), full_nonfull_union f hcap,
    sum_binPrimary, htotal]

theorem negativeFullBins_card_le (f : ι → Fin N) (p : ι → ℤ) (B c P0 : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c)
    (hp : ∀ i, p i ≤ (P0 : ℤ)) (htotal : ∑ i, p i = 0)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    (negativeFullBins f p).card ≤ 25 * c * P0 := by
  have hnegative : ((negativeFullBins f p).card : ℤ) ≤
      -(∑ b ∈ fullBins f, binPrimary f p b) := by
    calc
      ((negativeFullBins f p).card : ℤ) = ∑ _ ∈ negativeFullBins f p, (1 : ℤ) := by simp
      _ = ∑ b ∈ fullBins f, if binPrimary f p b < 0 then (1 : ℤ) else 0 := by
        rw [negativeFullBins, Finset.sum_filter]
      _ ≤ ∑ b ∈ fullBins f, -binPrimary f p b := by
        apply Finset.sum_le_sum
        intro b hb
        have h := hfull b (Finset.mem_filter.mp hb).2
        split_ifs <;> omega
      _ = _ := Finset.sum_neg_distrib (fun b => binPrimary f p b)
  have hnonfull : (∑ b ∈ nonfullBins f, binPrimary f p b) ≤
      ((nonfullItems f).card : ℤ) * (P0 : ℤ) := by
    change (∑ b ∈ nonfullBins f, ∑ i ∈ fiber f b, p i) ≤ _
    rw [sum_fibers]
    calc
      (∑ i ∈ itemsIn f (nonfullBins f), p i) ≤
          ∑ _ ∈ itemsIn f (nonfullBins f), (P0 : ℤ) :=
        Finset.sum_le_sum fun i _ => hp i
      _ = _ := by simp [nonfullItems]
  have hcons := primary_conservation f p hcap htotal
  have hitems : ((nonfullItems f).card : ℤ) ≤ (25 * c : ℕ) := by
    exact_mod_cast nonfullItems_card_le f B c hcard hcap hN
  have hscaled := mul_le_mul_of_nonneg_right hitems (Int.natCast_nonneg P0)
  have hbound : ((negativeFullBins f p).card : ℤ) ≤ ((25 * c * P0 : ℕ) : ℤ) := by
    push_cast
    push_cast at hscaled
    linarith
  exact_mod_cast hbound

variable [DecidableEq ι] in
theorem outsideZeroFullItems_eq (f : ι → Fin N) (p : ι → ℤ)
    (hcap : ∀ b, (fiber f b).card ≤ 5)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    outsideZeroFullItems f p = nonfullItems f ∪ itemsIn f (negativeFullBins f p) := by
  ext i
  simp only [outsideZeroFullItems, nonfullItems, itemsIn, negativeFullBins,
    nonfullBins, fullBins, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := hcap (f i)
  have hs := hfull (f i)
  omega

theorem loss_items_disjoint (f : ι → Fin N) (p : ι → ℤ) :
    Disjoint (nonfullItems f) (itemsIn f (negativeFullBins f p)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [nonfullItems, itemsIn, negativeFullBins, nonfullBins, fullBins,
    Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  omega

variable [DecidableEq ι] in
theorem primary_loss_bound (f : ι → Fin N) (p : ι → ℤ) (B c P0 : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c)
    (hp : ∀ i, |p i| < (P0 : ℤ)) (htotal : ∑ i, p i = 0)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    (nonfullItems f).card ≤ 25 * c ∧
    (negativeFullBins f p).card ≤ 25 * c * P0 ∧
    (outsideZeroFullItems f p).card ≤ 25 * c * (1 + 5 * P0) ∧
    (outsideZeroFullItems f p).card < 25 * (c + 1) * (1 + 5 * P0) := by
  have hnf := nonfullItems_card_le f B c hcard hcap hN
  have hneg := negativeFullBins_card_le f p B c P0 hcard hcap hN
    (fun i => (le_abs_self (p i)).trans (hp i).le) htotal hfull
  have hni := card_itemsIn_le f hcap (negativeFullBins f p)
  have hbad : (outsideZeroFullItems f p).card ≤ 25 * c * (1 + 5 * P0) := by
    rw [outsideZeroFullItems_eq f p hcap hfull,
      Finset.card_union_of_disjoint (loss_items_disjoint f p)]
    nlinarith
  refine ⟨hnf, hneg, hbad, hbad.trans_lt ?_⟩
  nlinarith

end BinPackingGap.PrimaryLoss

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalar
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.InventoryData.roleCopiesFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

theorem labelWeight_strictMono {n : ℕ} : StrictMono (@labelWeight n) := by
  intro x y hxy
  change (3 : ℤ) ^ (x.val + 1) < (3 : ℤ) ^ (y.val + 1)
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 3)
    (Nat.add_lt_add_right hxy 1)

theorem labelWeight_mono {n : ℕ} {x a : Fin n} (h : x ≤ a) :
    labelWeight x ≤ labelWeight a :=
  labelWeight_strictMono.monotone h

theorem labelWeight_gap {n : ℕ} {a x : Fin n} (h : a < x) :
    3 * labelWeight a ≤ labelWeight x := by
  have hax : a.val + 1 ≤ x.val := Nat.succ_le_of_lt h
  have hpow : (3 : ℤ) ^ ((a.val + 1) + 1) ≤ (3 : ℤ) ^ (x.val + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3)
      (Nat.add_le_add_right hax 1)
  calc
    3 * labelWeight a = (3 : ℤ) ^ ((a.val + 1) + 1) := by
      change (3 : ℤ) * (3 : ℤ) ^ (a.val + 1) = _
      rw [pow_succ (3 : ℤ) (a.val + 1), mul_comm]
    _ ≤ labelWeight x := hpow

theorem labelSecondary_nonpos_bounds {n : ℕ} {x d a : Fin n}
    (hq : labelSecondary x d a ≤ 0) : x ≤ a ∧ d ≤ a := by
  have ha := labelWeight_pos a
  have hx := labelWeight_pos x
  have hd := labelWeight_pos d
  change labelWeight x + labelWeight d - 2 * labelWeight a ≤ 0 at hq
  constructor
  · by_contra hxa
    have hgap := labelWeight_gap (lt_of_not_ge hxa)
    linarith
  · by_contra hda
    have hgap := labelWeight_gap (lt_of_not_ge hda)
    linarith

theorem labelSecondary_nonpos_iff {n : ℕ} {x d a : Fin n} :
    labelSecondary x d a ≤ 0 ↔ x ≤ a ∧ d ≤ a := by
  constructor
  · exact labelSecondary_nonpos_bounds
  · rintro ⟨hx, hd⟩
    have hqx := labelWeight_mono hx
    have hqd := labelWeight_mono hd
    unfold labelSecondary
    linarith

open scoped BigOperators

end

section

theorem primary_tail_lt (n : ℕ) :
    mu n * (10 * (3 : ℚ) ^ n) + nu n * 30 < gamma := by
  have heq : mu n * (10 * (3 : ℚ) ^ n) = 10 * gamma / 1000 := by
    rw [← mul_assoc, mul_comm (mu n) 10, mul_assoc, mu_mul_labelBound]
    ring
  rw [heq]
  have hn := nu_le_gamma_div n
  have hg := gamma_pos
  nlinarith

theorem secondary_tail_lt (n : ℕ) : nu n * 30 < mu n := by
  have hμ := mu_pos n
  unfold nu
  nlinarith

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

theorem mem_table_bin_iff (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (i : I.Item) :
    i ∈ p.binItems t.val ↔ ∃ r, p.itemAtRole subclass t r = i := by
  constructor
  · intro hi
    refine ⟨(p.tableEquiv subclass t).symm ⟨i, hi⟩, ?_⟩
    simp [itemAtRole]
  · rintro ⟨r, rfl⟩
    exact p.itemAtRole_mem subclass t r

theorem itemAtRole_eq_of_mem (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) (i : I.Item)
    (hi : i ∈ p.binItems t.val) (hr : (subclass i).role = r) :
    p.itemAtRole subclass t r = i := by
  obtain ⟨s, hs⟩ := (p.mem_table_bin_iff subclass t i).mp hi
  have hsr : s = r := by
    rw [← hs, p.itemAtRole_role] at hr
    exact hr
  simpa only [hsr] using hs

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

theorem secondaryTotal_rat_abs_le {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) :
    |(secondaryTotal s label : ℚ)| ≤ 10 * (3 : ℚ) ^ n := by
  calc
    _ = |∑ i, (secondaryScore (s i) (label i) : ℚ)| := by simp [secondaryTotal]
    _ ≤ ∑ i, |(secondaryScore (s i) (label i) : ℚ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, 2 * (3 : ℚ) ^ n :=
      Finset.sum_le_sum (fun i _ => secondaryScore_rat_abs_le (s i) (label i))
    _ = _ := by norm_num; ring

theorem coordinateTotal_abs_le (w : Fin 5 → ℚ) (hw : ∀ i, |w i| ≤ 6) :
    |coordinateTotal w| ≤ 30 := by
  calc
    _ ≤ ∑ i, |w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, (6 : ℚ) := Finset.sum_le_sum (fun i _ => hw i)
    _ = _ := by norm_num

theorem sum_primary_nonpos_of_feasible {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hw : ∀ i, |w i| ≤ 6)
    (hfeas : (∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) :
    primaryTotal s ≤ 0 := by
  by_contra h
  have hp : (1 : ℤ) ≤ primaryTotal s :=
    Int.add_one_le_iff.mpr (lt_of_not_ge h)
  have hpQ : (1 : ℚ) ≤ (primaryTotal s : ℚ) := by exact_mod_cast hp
  have hp' := mul_le_mul_of_nonneg_left hpQ gamma_pos.le
  have hq := mul_le_mul_of_nonneg_left
    (abs_le.mp (secondaryTotal_rat_abs_le s label)).1 (mu_pos n).le
  have hw' := mul_le_mul_of_nonneg_left
    (abs_le.mp (coordinateTotal_abs_le w hw)).1 (nu_pos n).le
  have htail := primary_tail_lt n
  rw [encodedSize_sum] at hfeas
  nlinarith only [hfeas, hp', hq, hw', htail]

theorem sum_secondary_nonpos_of_feasible {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hw : ∀ i, |w i| ≤ 6) (hp : primaryTotal s = 0)
    (hfeas : (∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) :
    secondaryTotal s label ≤ 0 := by
  by_contra h
  have hq : (1 : ℤ) ≤ secondaryTotal s label :=
    Int.add_one_le_iff.mpr (lt_of_not_ge h)
  have hqQ : (1 : ℚ) ≤ (secondaryTotal s label : ℚ) := by exact_mod_cast hq
  have hq' := mul_le_mul_of_nonneg_left hqQ (mu_pos n).le
  have hw' := mul_le_mul_of_nonneg_left
    (abs_le.mp (coordinateTotal_abs_le w hw)).1 (nu_pos n).le
  have htail := secondary_tail_lt n
  rw [encodedSize_sum, hp] at hfeas
  norm_num only [Int.cast_zero, mul_zero, add_zero] at hfeas
  nlinarith only [hfeas, hq', hw', htail]

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

theorem full_primary_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6)
    (j : Fin b) (hc : (p.binItems j).card = 5) :
    p.primaryTotal subclass j ≤ 0 := by
  let e := p.fiveEquiv j hc
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity j
  have hp := sum_primary_nonpos_of_feasible
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) (fun i => hw _) hcap
  change (∑ i : Fin 5, primaryScore (subclass (p.fiveEquiv j hc i).val)) ≤ 0 at hp
  rw [p.sum_fiveEquiv j hc (fun i => primaryScore (subclass i))] at hp
  exact hp

theorem table_secondary_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin subclass) :
    (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) ≤ 0 := by
  let e := p.fiveEquiv t.val t.property.1
  have hp : BinPackingGap.primaryTotal (fun i => subclass (e i).val) = 0 := by
    change (∑ i : Fin 5,
      primaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1 (fun i => primaryScore (subclass i))]
    exact t.property.2
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity t.val
  have hq := sum_secondary_nonpos_of_feasible
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) (fun i => hw _) hp hcap
  change (∑ i : Fin 5,
    secondaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)
      (label (p.fiveEquiv t.val t.property.1 i).val)) ≤ 0 at hq
  rw [p.sum_fiveEquiv t.val t.property.1
    (fun i => secondaryScore (subclass i) (label i))] at hq
  exact hq

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

theorem table_labels_le_anchor (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin subclass)
    (x d a : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel x d a r) :
    x ≤ a ∧ d ≤ a := by
  have hq := p.table_secondary_nonpos subclass label coordinate hsize hw t
  rw [p.table_secondary_eq subclass label t x d a hl] at hq
  exact labelSecondary_nonpos_iff.mp hq

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

theorem outsideTableItems_card_lt (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (B c : ℕ)
    (hcard : I.n = 5 * B) (hb : b ≤ B + c)
    (htotal : (∑ i, primaryScore (subclass i)) = 0) :
    (p.outsideTableItems subclass).card <
      25 * (c + 1) * (1 + 5 * primaryBound) := by
  classical
  have hlarge (i : I.Item) : (1 / 6 : ℚ) < I.size i := by
    rw [hsize]
    exact (encodedSize_mem_interval _ _ _ (hw i)).1
  have hcap := p.bin_card_le_five hlarge
  have hfull (j : Fin b) (hc : (PrimaryLoss.fiber p.assignment j).card = 5) :
      PrimaryLoss.binPrimary p.assignment (fun i => primaryScore (subclass i)) j ≤ 0 := by
    exact p.full_primary_nonpos subclass label coordinate hsize hw j hc
  have h := PrimaryLoss.primary_loss_bound p.assignment
    (fun i => primaryScore (subclass i)) B c primaryBound
    (by simpa using hcard) hcap hb (fun i => primaryScore_abs_lt (subclass i)) htotal hfull
  have hsets : p.outsideTableItems subclass =
      PrimaryLoss.outsideZeroFullItems p.assignment (fun i => primaryScore (subclass i)) := by
    ext i
    constructor
    · intro hi
      have hi' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩
    · intro hi
      have hi' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩
  rw [hsets]
  exact h.2.2.2

end Packing

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_CurrentMatches
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.InventoryData.roleCopiesFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace Coverage

variable {I : Instance} {b n : ℕ}

theorem edgeTuplesAt_subset_good (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    edgeTuplesAt p cls label v ⊆ goodTuplesAt p cls label v := by
  classical
  exact Finset.filter_subset _ _

@[simp] theorem roleItems_card (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) : (roleItems p cls s role).card = s.card :=
  Finset.card_image_of_injective s (p.itemAtRole_injective cls role)

end Coverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryScores
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

theorem sum_primaryScore_eq_zero_of_inventory {ι : Type*} [Fintype ι]
    (s : ι → Subclass) (B : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hrole : ∀ r : Role, roleCount s r = (B : ℤ))
    (htree : subclassCount s .tp + subclassCount s .tm = subclassCount s .ft)
    (hanchor : subclassCount s .z = subclassCount s .ft + subclassCount s .fm)
    (hglobal : subclassCount s .up + subclassCount s .um =
      subclassCount s .ft + subclassCount s .fm)
    (hlocal : subclassCount s .dm = subclassCount s .ft + subclassCount s .fm)
    (hminus : subclassCount s .tm = subclassCount s .um) :
    (∑ i, primaryScore (s i)) = 0 := by
  apply sum_primaryScore_eq_zero_of_coefficients
  have hr (r : Role) : (∑ i, primaryCoeff (roleCoeffIndex r) (s i)) = 0 := by
    rw [sum_primaryCoeff_role, hrole, hcard]
    push_cast
    ring
  intro j
  fin_cases j
  · simpa [roleCoeffIndex, Role.index] using hr .x
  · simpa [roleCoeffIndex, Role.index] using hr .anchor
  · simpa [roleCoeffIndex, Role.index] using hr .«global»
  · simpa [roleCoeffIndex, Role.index] using hr .«local»
  · simpa [roleCoeffIndex, Role.index] using hr .flag
  · change (∑ i, primaryCoeff (5 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_five s, htree, sub_self]
  · change (∑ i, primaryCoeff (6 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_six s, hanchor]
    ring
  · change (∑ i, primaryCoeff (7 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_seven s, hglobal]
    ring
  · change (∑ i, primaryCoeff (8 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_eight s, hlocal]
    ring
  · change (∑ i, primaryCoeff (9 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_nine s, hminus, sub_self]

end BinPackingGap

noncomputable section

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData)

theorem keyItem_injective : Function.Injective D.keyItem := by
  intro i j h
  exact Option.some.inj (by simpa only [D.keyData_keyItem] using congrArg D.keyData h)

theorem edgeResourceItem_injective : Function.Injective D.edgeResourceItem := by
  intro i j h
  exact Option.some.inj (by
    simpa only [D.edgeResourceData_edgeResourceItem] using congrArg D.edgeResourceData h)

theorem prefixJobIndex_injective (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Function.Injective (D.prefixJobIndex h hle) := by
  intro i j hij
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun x => x.1.1.1.val) hij
      · exact congrArg (fun x => x.1.1.2) hij
    · exact congrArg (fun x => x.1.2) hij
  · exact congrArg (fun x : ((D.Edge × Fin 2) × Fin D.R) × Fin D.d => x.2) hij

theorem earlierKeys_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierKeys h hle).card = 2 * D.d * D.R * h := by
  classical
  have hinj : Function.Injective (fun j : ((Fin h × Fin 2) × Fin D.R) × Fin D.d =>
      D.keyItem (D.allJobEquiv.symm (D.prefixJobIndex h hle j))) := by
    intro i j hij
    exact D.prefixJobIndex_injective h hle
      (D.allJobEquiv.symm.injective (D.keyItem_injective hij))
  rw [earlierKeys, Finset.card_image_of_injective _ hinj]
  simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm]

theorem mem_earlierKeys (h : ℕ) (hle : h ≤ D.graph.edges.length) (i : D.Item) :
    i ∈ D.earlierKeys h hle ↔
      ∃ j : Σ v : D.Vertex, D.JobCopy v,
        D.keyItem j = i ∧ (D.jobPosition j.2).1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨D.allJobEquiv.symm (D.prefixJobIndex h hle j), rfl, j.1.1.1.isLt⟩
  · rintro ⟨j, rfl, hj⟩
    let a := D.allJobEquiv j
    let x : ((Fin h × Fin 2) × Fin D.R) × Fin D.d :=
      ((⟨⟨a.1.1.1.val, hj⟩, a.1.1.2⟩, a.1.2), a.2)
    have hx : D.prefixJobIndex h hle x = a := by
      apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Fin.ext; rfl
          · rfl
        · rfl
      · rfl
    refine Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩
    rw [hx]
    exact congrArg D.keyItem (D.allJobEquiv.symm_apply_apply j)

theorem prefixWIndex_injective (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Function.Injective (D.prefixWIndex h hle) := by
  intro i j hij
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun x => x.1.1.val) hij
    · exact congrArg (fun x => x.1.2) hij
  · exact congrArg (fun x : (D.Edge × Bool) × Fin (D.d * D.R) => x.2) hij

theorem earlierW_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierW h hle).card = 2 * D.d * D.R * h := by
  classical
  have hinj : Function.Injective (fun w : (Fin h × Bool) × Fin (D.d * D.R) =>
      D.edgeResourceItem (D.prefixWIndex h hle w)) := by
    intro i j hij
    exact D.prefixWIndex_injective h hle (D.edgeResourceItem_injective hij)
  rw [earlierW, Finset.card_image_of_injective _ hinj]
  simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem mem_earlierW (h : ℕ) (hle : h ≤ D.graph.edges.length) (i : D.Item) :
    i ∈ D.earlierW h hle ↔
      ∃ w : (D.Edge × Bool) × Fin (D.d * D.R),
        D.edgeResourceItem w = i ∧ w.1.1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨D.prefixWIndex h hle w, rfl, w.1.1.isLt⟩
  · rintro ⟨w, rfl, hw⟩
    let x : (Fin h × Bool) × Fin (D.d * D.R) :=
      ((⟨w.1.1.val, hw⟩, w.1.2), w.2)
    have hx : D.prefixWIndex h hle x = w := by
      apply Prod.ext
      · apply Prod.ext
        · apply Fin.ext; rfl
        · rfl
      · rfl
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, congrArg D.edgeResourceItem hx⟩

end InventoryData
end BinPackingGap

end

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

private theorem subclassCount_by_role (subclass : Subclass) :
    subclassCount D.itemSubclass subclass =
      ∑ i : D.RoleCopies subclass.role,
        subclassIndicator (D.itemSubclass ⟨subclass.role, i⟩) subclass := by
  classical
  unfold subclassCount
  rw [Fintype.sum_sigma]
  refine Finset.sum_eq_single subclass.role ?_ ?_
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro hi
    apply hr
    calc
      r = (D.itemSubclass ⟨r, i⟩).role := (D.itemSubclass_role ⟨r, i⟩).symm
      _ = subclass.role := congrArg Subclass.role hi
  · simp

theorem roleCount_itemSubclass (hk : D.k ≤ D.graph.n) (r : Role) :
    roleCount D.itemSubclass r = (D.B : ℤ) := by
  classical
  simp only [roleCount, D.itemSubclass_role, itemRole, Fintype.sum_sigma]
  have hrole : (∑ s : Role, ∑ _ : D.RoleCopies s,
      if s = r then (1 : ℤ) else 0) = (Fintype.card (D.RoleCopies r) : ℤ) := by
    simp
  rw [hrole, D.card_roleCopies hk]

theorem subclassCount_tp :
    subclassCount D.itemSubclass .tp = D.graph.n * (D.tPlus : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.RowAt v), subclassIndicator (D.itemSubclass ⟨.x, i⟩) .tp) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, rowSubclass, TreeRow, treeSubclass, subclassIndicator,
    Fintype.sum_sum_type, tPlus, Nat.cast_add, Nat.cast_mul, mul_add,
    mul_comm, mul_left_comm]

theorem subclassCount_tm :
    subclassCount D.itemSubclass .tm = D.graph.n * (D.tMinus : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.RowAt v), subclassIndicator (D.itemSubclass ⟨.x, i⟩) .tm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, rowSubclass, TreeRow, treeSubclass, subclassIndicator,
    Fintype.sum_sum_type, tMinus, Nat.cast_mul, mul_comm, mul_left_comm]

theorem subclassCount_z :
    subclassCount D.itemSubclass .z = ∑ v : D.Vertex, ((D.t + D.J v : ℕ) : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.AnchorAt v), subclassIndicator (D.itemSubclass ⟨.anchor, i⟩) .z) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_mBase]

theorem subclassCount_up (hk : D.k ≤ D.graph.n) :
    subclassCount D.itemSubclass .up = (D.plusSlots : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : GlobalSpecies D.graph, Fin (D.globalStock t)), subclassIndicator (D.itemSubclass ⟨.«global», i⟩) .up) = _
  rw [Fintype.sum_sigma]
  have h := congrArg (fun x : ℕ => (x : ℤ)) (D.up_species_total hk)
  simpa [subclassCount, itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sigma, Role.sum_univ, GlobalSpecies.sum_univ,
    Fintype.sum_sum_type] using h

theorem subclassCount_um :
    subclassCount D.itemSubclass .um = (D.minusSlots : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : GlobalSpecies D.graph, Fin (D.globalStock t)), subclassIndicator (D.itemSubclass ⟨.«global», i⟩) .um) = _
  rw [Fintype.sum_sigma]
  have h := congrArg (fun x : ℕ => (x : ℤ)) D.um_species_total
  simpa [subclassCount, itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sigma, Role.sum_univ, GlobalSpecies.sum_univ,
    Fintype.sum_sum_type] using h

theorem subclassCount_dm :
    subclassCount D.itemSubclass .dm = ∑ v : D.Vertex, ((D.t + D.J v : ℕ) : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.LocalAt v), subclassIndicator (D.itemSubclass ⟨.«local», i⟩) .dm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_dmAt]

theorem subclassCount_ft :
    subclassCount D.itemSubclass .ft = (D.treeFlags : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : FlagSpecies, Fin (D.flagStock t)), subclassIndicator (D.itemSubclass ⟨.flag, i⟩) .ft) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator, FlagSpecies.sum_univ, flagStock]
  change Fintype.card (Fin D.treeFlags) = D.treeFlags
  exact Fintype.card_fin _

theorem subclassCount_fm :
    subclassCount D.itemSubclass .fm = (D.jobFlags : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : FlagSpecies, Fin (D.flagStock t)), subclassIndicator (D.itemSubclass ⟨.flag, i⟩) .fm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator, FlagSpecies.sum_univ, flagStock]
  change Fintype.card (Fin D.jobFlags) = D.jobFlags
  exact Fintype.card_fin _

theorem total_primaryScore_eq_zero (hk : D.k ≤ D.graph.n) :
    (∑ i : D.Item, primaryScore (D.itemSubclass i)) = 0 := by
  apply sum_primaryScore_eq_zero_of_inventory D.itemSubclass D.B
    (D.card_item hk) (D.roleCount_itemSubclass hk)
  · rw [D.subclassCount_tp, D.subclassCount_tm, D.subclassCount_ft]
    simp [treeFlags, t, Nat.cast_mul, Nat.cast_add, mul_add]
  · rw [D.subclassCount_z, D.subclassCount_ft, D.subclassCount_fm]
    simp [treeFlags, jobFlags, Nat.cast_mul, Nat.cast_sum, Nat.cast_add,
      Finset.sum_add_distrib]
  · rw [D.subclassCount_up hk, D.subclassCount_um, D.subclassCount_ft,
      D.subclassCount_fm, D.plusSlots_eq]
    simp [minusSlots, treeFlags, jobFlags, t, Nat.cast_mul, Nat.cast_add,
      Nat.cast_sum, mul_add]
    ring
  · rw [D.subclassCount_dm, D.subclassCount_ft, D.subclassCount_fm]
    simp [treeFlags, jobFlags, Nat.cast_mul, Nat.cast_sum, Nat.cast_add,
      Finset.sum_add_distrib]
  · rw [D.subclassCount_tm, D.subclassCount_um]
    simp [minusSlots]

theorem labelledRoleCount_x (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .x v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_rowAt]

theorem labelledRoleCount_anchor (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .anchor v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_anchorAt]

theorem labelledRoleCount_local (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .«local» v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_localAt]

end InventoryData

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_LabelConservation
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

namespace LabelConservation

open scoped BigOperators

variable {n : ℕ}
variable {T A R D : Type*}
variable [Fintype T] [Fintype A] [Fintype R] [Fintype D]
variable [DecidableEq A] [DecidableEq R] [DecidableEq D]

omit [DecidableEq A] [DecidableEq R] in
theorem prefix_inventory_eq (labelA : A → Fin n) (labelR : R → Fin n)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (prefixItems labelA h).card = (prefixItems labelR h).card := by
  let labels : Finset (Fin n) := Finset.univ.filter fun v => v.val < h
  have hA := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset A)
    labels labelA
  have hR := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset R)
    labels labelR
  have hsum : (∑ v ∈ labels, (Finset.univ.filter fun a => labelA a = v).card) =
      ∑ v ∈ labels, (Finset.univ.filter fun r => labelR r = v).card := by
    exact Finset.sum_congr rfl fun v _ => hInv v
  simpa only [labels, Finset.mem_filter, Finset.mem_univ, true_and, prefixItems]
    using hA.symm.trans (hsum.trans hR)

theorem outside_add_selected_eq (label : A → Fin n) (f : T → A)
    (hf : Function.Injective f) (h : ℕ) :
    (prefixOutside label f h).card + (prefixItems (label ∘ f) h).card =
      (prefixItems label h).card := by
  have hsplit := Finset.card_sdiff_add_card_inter
    (prefixItems label h) (Finset.univ.image f)
  have hout : prefixItems label h \ Finset.univ.image f = prefixOutside label f h := by
    ext x
    simp [prefixItems, prefixOutside, outsideItems, and_comm]
  have hin : prefixItems label h ∩ Finset.univ.image f =
      (Finset.univ.image f).filter (fun x => (label x).val < h) := by
    ext x
    simp [prefixItems, and_comm]
  rw [hout, hin, Finset.filter_image, Finset.card_image_of_injective _ hf] at hsplit
  simpa only [prefixItems, Function.comp_apply] using hsplit

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
theorem selected_add_exports_eq (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val) (h : ℕ) :
    (prefixItems (labelA ∘ anchor) h).card + (exports labelA labelR anchor role h).card =
      (prefixItems (labelR ∘ role) h).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := prefixItems (labelR ∘ role) h) (fun t => (labelA (anchor t)).val < h)
  have hin : (prefixItems (labelR ∘ role) h).filter
      (fun t => (labelA (anchor t)).val < h) = prefixItems (labelA ∘ anchor) h := by
    ext t
    simp only [Finset.mem_filter, prefixItems, Finset.mem_univ, true_and,
      Function.comp_apply]
    exact ⟨fun ht => ht.2, fun ht => ⟨lt_of_le_of_lt (hle t) ht, ht⟩⟩
  have hout : (prefixItems (labelR ∘ role) h).filter
      (fun t => ¬ (labelA (anchor t)).val < h) = exports labelA labelR anchor role h := by
    ext t
    simp [prefixItems, exports]
  rw [hin, hout] at hsplit
  exact hsplit

theorem exports_add_outsideRole_eq_outsideAnchor
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (exports labelA labelR anchor role h).card + (prefixOutside labelR role h).card =
      (prefixOutside labelA anchor h).card := by
  have hA := outside_add_selected_eq labelA anchor hAnchor h
  have hR := outside_add_selected_eq labelR role hRole h
  have hE := selected_add_exports_eq labelA labelR anchor role hle h
  have hI := prefix_inventory_eq labelA labelR hInv h
  omega

theorem exports_card_le_outside
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (exports labelA labelR anchor role h).card ≤ (outsideItems anchor).card := by
  have hcon := exports_add_outsideRole_eq_outsideAnchor
    labelA labelR anchor role hAnchor hRole hle hInv h
  have hout : (prefixOutside labelA anchor h).card ≤ (outsideItems anchor).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
theorem labelDefects_subset_exports
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val) (v : Fin n) :
    labelDefects labelA labelR anchor role v ⊆ exports labelA labelR anchor role v.val := by
  intro t ht
  obtain ⟨ha, hr⟩ := (Finset.mem_filter.mp ht).2
  have hl := hle t
  rw [ha] at hl
  have hn : (labelR (role t)).val ≠ v.val := fun he => hr (Fin.ext he)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · omega
  · simp [ha]

theorem labelDefects_card_le_outside
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (v : Fin n) :
    (labelDefects labelA labelR anchor role v).card ≤ (outsideItems anchor).card := by
  exact (Finset.card_le_card (labelDefects_subset_exports labelA labelR anchor role hle v)).trans
    (exports_card_le_outside labelA labelR anchor role hAnchor hRole hle hInv v.val)

omit [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D] in
theorem mem_badAnchors_iff
    (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D)
    (hAnchor : Function.Injective anchor) (v : Fin n) (a : A) :
    a ∈ badAnchors labelA labelR labelD anchor role localRole v ↔
      labelA a = v ∧
        ¬ ∃ t, anchor t = a ∧ labelR (role t) = v ∧ labelD (localRole t) = v := by
  constructor
  · intro hbad
    rcases Finset.mem_union.mp hbad with hleft | hd
    · rcases Finset.mem_union.mp hleft with ho | hr
      · obtain ⟨hoa, hv⟩ := Finset.mem_filter.mp ho
        refine ⟨hv, ?_⟩
        rintro ⟨t, hat, _, _⟩
        exact (Finset.mem_sdiff.mp hoa).2
          (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, hat⟩)
      · obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hr
        obtain ⟨hva, hvr⟩ := (Finset.mem_filter.mp ht).2
        refine ⟨by simpa only [hat] using hva, ?_⟩
        rintro ⟨u, hua, hur, _⟩
        have htu : t = u := hAnchor (hat.trans hua.symm)
        exact hvr (by simpa only [htu] using hur)
    · obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hd
      obtain ⟨hva, hvd⟩ := (Finset.mem_filter.mp ht).2
      refine ⟨by simpa only [hat] using hva, ?_⟩
      rintro ⟨u, hua, _, hud⟩
      have htu : t = u := hAnchor (hat.trans hua.symm)
      exact hvd (by simpa only [htu] using hud)
  · rintro ⟨hv, hnot⟩
    by_cases ha : a ∈ Finset.univ.image anchor
    · obtain ⟨t, _, hat⟩ := Finset.mem_image.mp ha
      have htv : labelA (anchor t) = v := by simpa only [hat] using hv
      by_cases hr : labelR (role t) = v
      · have hd : labelD (localRole t) ≠ v := fun hd => hnot ⟨t, hat, hr, hd⟩
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, htv, hd⟩, hat⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, htv, hr⟩, hat⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩, hv⟩

theorem badAnchors_card_le_three_mul
    (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hLocal : Function.Injective localRole)
    (hleR : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hleD : ∀ t, (labelD (localRole t)).val ≤ (labelA (anchor t)).val)
    (hInvR : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card)
    (hInvD : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun d => labelD d = v).card)
    (K : ℕ) (hOutside : (outsideItems anchor).card ≤ K) (v : Fin n) :
    (badAnchors labelA labelR labelD anchor role localRole v).card ≤ 3 * K := by
  have hR := labelDefects_card_le_outside labelA labelR anchor role hAnchor hRole hleR hInvR v
  have hD := labelDefects_card_le_outside labelA labelD anchor localRole
    hAnchor hLocal hleD hInvD v
  have hO : ((outsideItems anchor).filter fun a => labelA a = v).card ≤
      (outsideItems anchor).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hRi := Finset.card_image_le (s := labelDefects labelA labelR anchor role v) (f := anchor)
  have hDi := Finset.card_image_le (s := labelDefects labelA labelD anchor localRole v)
    (f := anchor)
  have hU := Finset.card_union_le
    ((outsideItems anchor).filter fun a => labelA a = v)
    ((labelDefects labelA labelR anchor role v).image anchor)
  have hV := Finset.card_union_le
    (((outsideItems anchor).filter fun a => labelA a = v) ∪
      (labelDefects labelA labelR anchor role v).image anchor)
    ((labelDefects labelA labelD anchor localRole v).image anchor)
  unfold badAnchors
  omega

end LabelConservation
end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_GoodAnchorBound
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

variable {I : Instance} {b n : ℕ}

theorem roleItem_label_count (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (r : Role)
    (roleLabel : RoleItem cls r → Fin n)
    (hspec : ∀ i, label i.val = some (roleLabel i)) (v : Fin n) :
    ((Finset.univ.filter fun i => roleLabel i = v).card : ℤ) =
      labelledRoleCount cls label r v := by
  classical
  have himage : (Finset.univ.filter fun i => roleLabel i = v).image Subtype.val =
      Finset.univ.filter (fun i => (cls i).role = r ∧ label i = some v) := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have hv := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property,
        (hspec a).trans (congrArg some hv)⟩
    · intro hi
      obtain ⟨hr, hv⟩ := (Finset.mem_filter.mp hi).2
      let a : RoleItem cls r := ⟨i, hr⟩
      have ha : roleLabel a = v := Option.some.inj ((hspec a).symm.trans hv)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
  have hcard : (Finset.univ.filter fun i => roleLabel i = v).card =
      (Finset.univ.filter fun i => (cls i).role = r ∧ label i = some v).card := by
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [hcard]
  simp [labelledRoleCount]

namespace RoleLabelData

theorem row_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.row i = v).card : ℤ) =
      labelledRoleCount cls label .x v :=
  roleItem_label_count cls label .x L.row L.row_spec v

theorem anchor_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.anchor i = v).card : ℤ) =
      labelledRoleCount cls label .anchor v :=
  roleItem_label_count cls label .anchor L.anchor L.anchor_spec v

theorem local_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.localLabel i = v).card : ℤ) =
      labelledRoleCount cls label .«local» v :=
  roleItem_label_count cls label .«local» L.localLabel L.local_spec v

end RoleLabelData

namespace Packing

theorem roleItemAt_injective (p : Packing I b) (cls : I.Item → Subclass) (r : Role) :
    Function.Injective (p.roleItemAt cls r) := by
  intro t u h
  exact p.itemAtRole_injective cls r (congrArg Subtype.val h)

theorem roleItemAt_labels (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (t : p.TableBin cls) (r : Role) :
    label (p.itemAtRole cls t r) = tableRoleLabel
      (L.row (p.roleItemAt cls .x t))
      (L.localLabel (p.roleItemAt cls .«local» t))
      (L.anchor (p.roleItemAt cls .anchor t)) r := by
  cases r with
  | x => exact L.row_spec (p.roleItemAt cls .x t)
  | anchor => exact L.anchor_spec (p.roleItemAt cls .anchor t)
  | «global» => exact L.global_spec (p.roleItemAt cls .«global» t)
  | «local» => exact L.local_spec (p.roleItemAt cls .«local» t)
  | flag => exact L.flag_spec (p.roleItemAt cls .flag t)

theorem roleItemAt_labels_le (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (cls i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin cls) :
    L.row (p.roleItemAt cls .x t) ≤ L.anchor (p.roleItemAt cls .anchor t) ∧
      L.localLabel (p.roleItemAt cls .«local» t) ≤ L.anchor (p.roleItemAt cls .anchor t) :=
  p.table_labels_le_anchor cls label coordinate hsize hw t _ _ _
    (p.roleItemAt_labels cls label L t)

theorem outside_roleItems_image_subset (p : Packing I b) (cls : I.Item → Subclass)
    (r : Role) :
    (LabelConservation.outsideItems (p.roleItemAt cls r)).image Subtype.val ⊆
      p.outsideTableItems cls := by
  classical
  intro i hi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro ht
  have haout := (Finset.mem_sdiff.mp ha).2
  apply haout
  let t : p.TableBin cls := ⟨p.assignment a.val, ht⟩
  refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  exact p.itemAtRole_eq_of_mem cls t r a.val (p.mem_own_bin a.val) a.property

theorem outside_roleItems_card_le (p : Packing I b) (cls : I.Item → Subclass) (r : Role) :
    (LabelConservation.outsideItems (p.roleItemAt cls r)).card ≤
      (p.outsideTableItems cls).card := by
  classical
  rw [← Finset.card_image_of_injective
    (LabelConservation.outsideItems (p.roleItemAt cls r)) Subtype.val_injective]
  exact Finset.card_le_card (p.outside_roleItems_image_subset cls r)

end Packing

namespace Coverage

theorem goodTuplesAt_iff_roleLabels (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (v : Fin n) (t : p.TableBin cls) :
    t ∈ goodTuplesAt p cls label v ↔
      L.anchor (p.roleItemAt cls .anchor t) = v ∧
        L.row (p.roleItemAt cls .x t) = v ∧
          L.localLabel (p.roleItemAt cls .«local» t) = v := by
  rw [mem_goodTuplesAt]
  have hx := L.row_spec (p.roleItemAt cls .x t)
  have ha := L.anchor_spec (p.roleItemAt cls .anchor t)
  have hd := L.local_spec (p.roleItemAt cls .«local» t)
  change label (p.itemAtRole cls t .x) = some _ at hx
  change label (p.itemAtRole cls t .anchor) = some _ at ha
  change label (p.itemAtRole cls t .«local») = some _ at hd
  simp only [Packing.IsGoodTableBin, hx, ha, hd, Option.some.injEq]
  constructor
  · rintro ⟨⟨hr, hl⟩, hv⟩
    exact ⟨hv, hr.trans hv, hl.trans hv⟩
  · rintro ⟨hv, hr, hl⟩
    exact ⟨⟨hr.trans hv.symm, hl.trans hv.symm⟩, hv⟩

theorem mem_badRoleAnchors (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (v : Fin n) (a : RoleItem cls .anchor) :
    a ∈ badRoleAnchors p cls label L v ↔ L.anchor a = v ∧
      ¬ ∃ t, p.roleItemAt cls .anchor t = a ∧
        L.row (p.roleItemAt cls .x t) = v ∧
          L.localLabel (p.roleItemAt cls .«local» t) = v := by
  classical
  exact LabelConservation.mem_badAnchors_iff L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local»)
    (p.roleItemAt_injective cls .anchor) v a

theorem badRoleAnchors_image_eq (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    (badRoleAnchors p cls label L v).image Subtype.val = badAnchorsAt p cls label v := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hv, hnot⟩ := (mem_badRoleAnchors p cls label L v a).mp ha
    apply (mem_badAnchorsAt p cls label v a.val).mpr
    refine ⟨(mem_anchorItemsAt cls label v a.val).mpr ⟨a.property, ?_⟩, ?_⟩
    · rw [L.anchor_spec, hv]
    · intro hgood
      obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hgood
      obtain ⟨_, hr, hd⟩ := (goodTuplesAt_iff_roleLabels p cls label L v t).mp ht
      exact hnot ⟨t, Subtype.ext hat, hr, hd⟩
  · intro hi
    obtain ⟨hiA, hiBad⟩ := (mem_badAnchorsAt p cls label v i).mp hi
    obtain ⟨hr, hv⟩ := (mem_anchorItemsAt cls label v i).mp hiA
    let a : RoleItem cls .anchor := ⟨i, hr⟩
    have hva : L.anchor a = v := Option.some.inj ((L.anchor_spec a).symm.trans hv)
    refine Finset.mem_image.mpr ⟨a, ?_, rfl⟩
    apply (mem_badRoleAnchors p cls label L v a).mpr
    refine ⟨hva, ?_⟩
    rintro ⟨t, hat, hrow, hlocal⟩
    apply hiBad
    refine Finset.mem_image.mpr ⟨t, ?_, congrArg Subtype.val hat⟩
    apply (goodTuplesAt_iff_roleLabels p cls label L v t).mpr
    exact ⟨by simpa only [hat] using hva, hrow, hlocal⟩

@[simp] theorem badRoleAnchors_card (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    (badRoleAnchors p cls label L v).card = (badAnchorsAt p cls label v).card := by
  classical
  rw [← badRoleAnchors_image_eq p cls label L v,
    Finset.card_image_of_injective _ Subtype.val_injective]

variable (p : Packing I b) (cls : I.Item → Subclass)
variable (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
variable (coordinate : I.Item → ℚ)
variable (hsize : ∀ i, I.size i = encodedSize (cls i) (label i) (coordinate i))
variable (hw : ∀ i, |coordinate i| ≤ 6) (B c : ℕ)
variable (hcard : I.n = 5 * B) (hb : b ≤ B + c)
variable (htotal : (∑ i, primaryScore (cls i)) = 0)
variable (hInvR : ∀ v, (Finset.univ.filter fun a => L.anchor a = v).card =
  (Finset.univ.filter fun r => L.row r = v).card)
variable (hInvD : ∀ v, (Finset.univ.filter fun a => L.anchor a = v).card =
  (Finset.univ.filter fun d => L.localLabel d = v).card)

include L coordinate hsize hw B hcard hb htotal hInvR hInvD

theorem badAnchorsAt_card_le (v : Fin n) :
    (badAnchorsAt p cls label v).card ≤
      3 * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
  classical
  have hOutside := (p.outside_roleItems_card_le cls .anchor).trans
    (p.outsideTableItems_card_lt cls label coordinate hsize hw B c hcard hb htotal).le
  have hleR (t : p.TableBin cls) :
      (L.row (p.roleItemAt cls .x t)).val ≤
        (L.anchor (p.roleItemAt cls .anchor t)).val :=
    (p.roleItemAt_labels_le cls label L coordinate hsize hw t).1
  have hleD (t : p.TableBin cls) :
      (L.localLabel (p.roleItemAt cls .«local» t)).val ≤
        (L.anchor (p.roleItemAt cls .anchor t)).val :=
    (p.roleItemAt_labels_le cls label L coordinate hsize hw t).2
  have h := LabelConservation.badAnchors_card_le_three_mul L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local»)
    (p.roleItemAt_injective cls .anchor) (p.roleItemAt_injective cls .x)
    (p.roleItemAt_injective cls .«local») hleR hleD hInvR hInvD
    (25 * (c + 1) * (1 + 5 * primaryBound)) hOutside v
  change (badRoleAnchors p cls label L v).card ≤ _ at h
  simpa only [badRoleAnchors_card] using h

theorem badAnchors_global_card_le :
    ((Finset.univ : Finset (Fin n)).biUnion (badAnchorsAt p cls label)).card ≤
      3 * n * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
  classical
  calc
    _ ≤ ∑ v : Fin n, (badAnchorsAt p cls label v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n, 3 * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
      apply Finset.sum_le_sum
      intro v _
      exact badAnchorsAt_card_le p cls label L coordinate hsize hw B c
        hcard hb htotal hInvR hInvD v
    _ = _ := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end Coverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingSelections
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
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

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryPrefixConservation
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
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

theorem encodedCoordinate_abs_le_six (i : D.packingInstance.Item) :
    |D.encodedCoordinate i| ≤ 6 := D.itemCoordinate_abs_le_six _

theorem packingInstance_n (hk : D.k ≤ D.graph.n) :
    D.packingInstance.n = 5 * D.B := D.card_item hk

theorem encoded_primaryScore_sum_eq_zero (hk : D.k ≤ D.graph.n) :
    (∑ i : D.packingInstance.Item, primaryScore (D.encodedSubclass i)) = 0 := by
  change (∑ i, primaryScore (D.itemSubclass (D.itemEquiv.symm i))) = 0
  rw [D.itemEquiv.symm.sum_comp (fun i : D.Item => primaryScore (D.itemSubclass i))]
  exact D.total_primaryScore_eq_zero hk

theorem encoded_labelledRoleCount (r : Role) (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel r v =
      labelledRoleCount D.itemSubclass D.itemLabel r v := by
  unfold labelledRoleCount encodedSubclass encodedLabel
  exact D.itemEquiv.symm.sum_comp
    (fun i : D.Item => if (D.itemSubclass i).role = r ∧ D.itemLabel i = some v
      then (1 : ℤ) else 0)

theorem encoded_labelledRoleCount_x (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .x v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_x]

theorem encoded_labelledRoleCount_anchor (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .anchor v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_anchor]

theorem encoded_labelledRoleCount_local (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .«local» v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_local]

end InventoryData

end

namespace InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem roleLabelData_anchor_row_count (v : D.Vertex) :
    (Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card =
      (Finset.univ.filter fun i => D.roleLabelData.row i = v).card := by
  classical
  have h : ((Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card : ℤ) =
      ((Finset.univ.filter fun i => D.roleLabelData.row i = v).card : ℤ) := by
    rw [D.roleLabelData.anchor_count, D.roleLabelData.row_count,
      D.encoded_labelledRoleCount_anchor, D.encoded_labelledRoleCount_x]
  exact_mod_cast h

theorem roleLabelData_anchor_local_count (v : D.Vertex) :
    (Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card =
      (Finset.univ.filter fun i => D.roleLabelData.localLabel i = v).card := by
  classical
  have h : ((Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card : ℤ) =
      ((Finset.univ.filter fun i => D.roleLabelData.localLabel i = v).card : ℤ) := by
    rw [D.roleLabelData.anchor_count, D.roleLabelData.local_count,
      D.encoded_labelledRoleCount_anchor, D.encoded_labelledRoleCount_local]
  exact_mod_cast h

theorem badAnchors_global_card_le {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) :
    ((Finset.univ : Finset D.Vertex).biUnion
      (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel)).card ≤
      3 * D.graph.n * lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    Coverage.badAnchors_global_card_le p D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)
      D.roleLabelData_anchor_row_count D.roleLabelData_anchor_local_count

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryCoverage
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

theorem keyExpression_exact_position_edge (m R D L : ℕ)
    (key : Position m R) (nonpermit short : Bool) :
    keyExpression m R D L key key key.1 nonpermit short =
      delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0)) := by
  simp [keyExpression]

theorem long_exact_key_feasible_iff (m R D L : ℕ) (key : Position m R)
    (nonpermit : Bool) :
    keyExpression m R D L key key key.1 nonpermit false ≤ 0 ↔ nonpermit = false := by
  rw [keyExpression_exact_position_edge]
  have hd := delta_pos m R D L
  cases nonpermit <;> simp_all

theorem exact_long_key_resource {m R D L : ℕ}
    (key : Position m R) (edge : Fin m) (nonpermit : Bool)
    (h : keyExpression m R D L key key edge nonpermit false ≤ 0) :
    edge < key.1 ∨ (edge = key.1 ∧ nonpermit = false) := by
  have he := edge_order_of_key_feasible h
  rcases lt_or_eq_of_le he with hlt | heq
  · exact Or.inl hlt
  · right
    refine ⟨heq, ?_⟩
    subst edge
    exact (long_exact_key_feasible_iff m R D L key nonpermit).mp h

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

theorem exact_long_resource (w : EdgeTupleData p e t) (h : w.expression ≤ 0)
    (hpos : D.jobPosition w.row = D.jobPosition w.key) (hlong : w.short = false) :
    w.edge < (D.jobPosition w.key).1 ∨
      (w.edge = (D.jobPosition w.key).1 ∧ w.permit = true) := by
  have h' : Geometry.keyExpression D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition w.key) (D.jobPosition w.key) w.edge (!w.permit) false ≤ 0 := by
    simpa only [expression, hpos, hlong] using h
  have hresource := Geometry.exact_long_key_resource (D.jobPosition w.key) w.edge
    (!w.permit) h'
  cases hp : w.permit <;> simpa [hp] using hresource

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

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_EdgeLongConsumption
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace InventoryData

section

variable (D : InventoryData) {b : ℕ}

theorem earlierKeyItems_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierKeyItems h hle).card = 2 * D.d * D.R * h := by
  rw [earlierKeyItems, Finset.card_image_of_injective _ D.itemEquiv.injective,
    D.earlierKeys_card]

theorem earlierWItems_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierWItems h hle).card = 2 * D.d * D.R * h := by
  rw [earlierWItems, Finset.card_image_of_injective _ D.itemEquiv.injective,
    D.earlierW_card]

theorem mem_earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (i : D.packingInstance.Item) :
    i ∈ D.earlierKeyItems h hle ↔
      ∃ j : Σ v : D.Vertex, D.JobCopy v,
        D.itemEquiv (D.keyItem j) = i ∧ (D.jobPosition j.2).1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j, rfl, hj⟩ := (D.mem_earlierKeys h hle a).mp ha
    exact ⟨j, rfl, hj⟩
  · rintro ⟨j, rfl, hj⟩
    exact Finset.mem_image.mpr ⟨D.keyItem j,
      (D.mem_earlierKeys h hle _).mpr ⟨j, rfl, hj⟩, rfl⟩

theorem mem_earlierWItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (i : D.packingInstance.Item) :
    i ∈ D.earlierWItems h hle ↔
      ∃ w : (D.Edge × Bool) × Fin (D.d * D.R),
        D.itemEquiv (D.edgeResourceItem w) = i ∧ w.1.1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w, rfl, hw⟩ := (D.mem_earlierW h hle a).mp ha
    exact ⟨w, rfl, hw⟩
  · rintro ⟨w, rfl, hw⟩
    exact Finset.mem_image.mpr ⟨D.edgeResourceItem w,
      (D.mem_earlierW h hle _).mpr ⟨w, rfl, hw⟩, rfl⟩

@[simp] theorem keyItem_mem_earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemEquiv (D.keyItem j) ∈ D.earlierKeyItems h hle ↔
      (D.jobPosition j.2).1.val < h := by
  rw [D.mem_earlierKeyItems]
  constructor
  · rintro ⟨z, hz, hlt⟩
    have heq := D.keyItem_injective (D.itemEquiv.injective hz)
    subst z
    exact hlt
  · intro hlt
    exact ⟨j, rfl, hlt⟩

@[simp] theorem edgeResourceItem_mem_earlierWItems
    (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (w : (D.Edge × Bool) × Fin (D.d * D.R)) :
    D.itemEquiv (D.edgeResourceItem w) ∈ D.earlierWItems h hle ↔ w.1.1.val < h := by
  rw [D.mem_earlierWItems]
  constructor
  · rintro ⟨z, hz, hlt⟩
    have heq := D.edgeResourceItem_injective (D.itemEquiv.injective hz)
    simpa only [heq] using hlt
  · intro hlt
    exact ⟨w, rfl, hlt⟩

theorem earlierGoodKeyTuples_anchor_subset (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor ⊆
      D.earlierKeyItems h hle := by
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  exact ((D.mem_earlierGoodKeyTuples p h hle t).mp ht).2

theorem earlierGoodKeyTuples_edge (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.earlierGoodKeyTuples p h hle) :
    ∃ v, t ∈ Coverage.edgeTuplesAt p D.encodedSubclass D.encodedLabel v := by
  obtain ⟨hgood, hkey⟩ := (D.mem_earlierGoodKeyTuples p h hle t).mp ht
  obtain ⟨j, hj, _⟩ := (D.mem_earlierKeyItems h hle _).mp hkey
  have hlabel : D.encodedLabel (p.itemAtRole D.encodedSubclass t .anchor) = some j.1 := by
    rw [← hj]
    simp [encodedLabel]
  have hsub : D.encodedSubclass (p.itemAtRole D.encodedSubclass t .anchor) = .y := by
    rw [← hj]
    simp [encodedSubclass]
  have hpat : p.tablePattern D.encodedSubclass t = .edgeJob := by
    have hx := (p.itemAtRole_subclass D.encodedSubclass t .anchor).symm.trans hsub
    cases hp : p.tablePattern D.encodedSubclass t <;> simp_all [patternSubclass]
  exact ⟨j.1, (Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel j.1 t).mpr
    ⟨hgood, hlabel, hpat⟩⟩

theorem earlierGoodKeyTuples_global_subset (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .«global» ⊆
      D.earlierWItems h hle := by
  classical
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v, htv⟩ := D.earlierGoodKeyTuples_edge p h hle t ht
  obtain ⟨w, _, _, he⟩ := PackingCounts.edge_tuple_feasible p D.itemEquiv
    D.packingInstance_size_eq v t htv
  obtain ⟨j, hj, hjlt⟩ := (D.mem_earlierKeyItems h hle _).mp
    (((D.mem_earlierGoodKeyTuples p h hle t).mp ht).2)
  have hkey : D.itemEquiv (D.keyItem ⟨(PackingCounts.anchorCopy p D.itemEquiv t).1, w.key⟩) =
      p.itemAtRole D.encodedSubclass t .anchor := by
    have ha := congrArg
      (fun a : D.AnchorAt (PackingCounts.anchorCopy p D.itemEquiv t).1 =>
        D.itemEquiv (⟨.anchor,
          ⟨(PackingCounts.anchorCopy p D.itemEquiv t).1, a⟩⟩ : D.Item)) w.anchor_eq
    have heta := congrArg
      (fun a : Σ v : D.Vertex, D.AnchorAt v => D.itemEquiv (⟨.anchor, a⟩ : D.Item))
      (Sigma.eta (PackingCounts.anchorCopy p D.itemEquiv t))
    exact ha.symm.trans (heta.trans (PackingCounts.roleCopy_item p D.itemEquiv t .anchor))
  have hjEq := D.keyItem_injective (D.itemEquiv.injective (hkey.trans hj.symm))
  have hpos := congrArg (fun z : Σ v : D.Vertex, D.JobCopy v =>
    (D.jobPosition z.2).1.val) hjEq
  have hwe : w.edge.val < h := lt_of_le_of_lt he (by simpa only [hpos] using hjlt)
  apply (D.mem_earlierWItems h hle _).mpr
  refine ⟨((w.edge, w.permit), w.globalIndex), ?_, hwe⟩
  exact (congrArg (fun g : D.GlobalCopy => D.itemEquiv (⟨.«global», g⟩ : D.Item))
    w.global_eq.symm).trans (PackingCounts.roleCopy_item p D.itemEquiv t .«global»)

theorem remainingEarlierW_card_eq_missingKeys (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.remainingEarlierW p h hle).card =
      (D.earlierKeyItems h hle \
        Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor).card := by
  rw [remainingEarlierW, Finset.card_sdiff_of_subset (D.earlierGoodKeyTuples_global_subset p h hle),
    Finset.card_sdiff_of_subset (D.earlierGoodKeyTuples_anchor_subset p h hle),
    Coverage.roleItems_card, Coverage.roleItems_card, D.earlierWItems_card,
    D.earlierKeyItems_card]

theorem missingEarlierKeys_subset_bad (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    D.earlierKeyItems h hle \
      Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor ⊆
        (Finset.univ : Finset D.Vertex).biUnion
          (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel) := by
  classical
  intro i hi
  obtain ⟨hik, hin⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨j, hj, _⟩ := (D.mem_earlierKeyItems h hle i).mp hik
  apply Finset.mem_biUnion.mpr
  refine ⟨j.1, Finset.mem_univ _, ?_⟩
  apply (Coverage.mem_badAnchorsAt p D.encodedSubclass D.encodedLabel j.1 i).mpr
  constructor
  · apply (Coverage.mem_anchorItemsAt D.encodedSubclass D.encodedLabel j.1 i).mpr
    rw [← hj]
    simp [encodedSubclass, encodedLabel, Subclass.role]
  · intro hgood
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hgood
    apply hin
    refine Finset.mem_image.mpr ⟨t, ?_, hti⟩
    apply (D.mem_earlierGoodKeyTuples p h hle t).mpr
    refine ⟨((Coverage.mem_goodTuplesAt p D.encodedSubclass D.encodedLabel j.1 t).mp ht).1, ?_⟩
    simpa only [hti] using hik

theorem remainingEarlierW_card_le {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.remainingEarlierW p h hle).card ≤ 3 * D.graph.n * lossAllowance c := by
  rw [D.remainingEarlierW_card_eq_missingKeys]
  exact (Finset.card_le_card (D.missingEarlierKeys_subset_bad p h hle)).trans
    (D.badAnchors_global_card_le hk p hb)

end

open scoped BigOperators
open PackingCounts

variable (D : InventoryData) {b : ℕ}

theorem edgeLongTuplesAt_disjoint (p : Packing D.packingInstance b) (edge : D.Edge)
    {q r : Fin 2 × Fin D.R} (hne : q ≠ r) :
    Disjoint (D.edgeLongTuplesAt p edge q) (D.edgeLongTuplesAt p edge r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t hq hr
  obtain ⟨hGq, hkeyq, _, _⟩ := (D.mem_edgeLongTuplesAt p edge q t).mp hq
  obtain ⟨hGr, hkeyr, _, _⟩ := (D.mem_edgeLongTuplesAt p edge r t).mp hr
  have hlq := ((Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge q.1) t).mp hGq).2.1
  have hlr := ((Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge r.1) t).mp hGr).2.1
  have hside : q.1 = r.1 := D.graph.endpoint_injective edge
    (Option.some.inj (hlq.symm.trans hlr))
  have hrep : q.2 = r.2 := congrArg (fun z : D.Edge × Fin D.R => z.2)
    ((Geometry.baseline_eq_iff (r := (edge, q.2)) (s := (edge, r.2))).mp
      (hkeyq.symm.trans hkeyr))
  exact hne (Prod.ext hside hrep)

theorem edgeLongTuples_card (p : Packing D.packingInstance b) (edge : D.Edge)
    (J : Finset (Fin D.R)) :
    (D.edgeLongTuples p edge J).card =
      ∑ side : Fin 2, ∑ rep ∈ J, (D.edgeLongTuplesAt p edge (side, rep)).card := by
  classical
  have hdis : ∀ q ∈ (Finset.univ : Finset (Fin 2)).product J,
      ∀ r ∈ (Finset.univ : Finset (Fin 2)).product J,
        q ≠ r → Disjoint (D.edgeLongTuplesAt p edge q) (D.edgeLongTuplesAt p edge r) := by
    intro q _ r _ hne
    exact D.edgeLongTuplesAt_disjoint p edge hne
  rw [edgeLongTuples, Finset.card_biUnion hdis]
  exact Finset.sum_product (Finset.univ : Finset (Fin 2)) J
    (fun q : Fin 2 × Fin D.R => (D.edgeLongTuplesAt p edge q).card)

theorem edgeLongTuplesAt_witness (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    ∃ w : EdgeTupleData p D.itemEquiv t, w.expression ≤ 0 ∧
      D.jobPosition w.key = (edge, q.2) ∧
      D.jobPosition w.row = (edge, q.2) ∧ w.short = false := by
  obtain ⟨hG, hkey, hrow, hshort⟩ := (D.mem_edgeLongTuplesAt p edge q t).mp ht
  obtain ⟨w, hf, _, _⟩ := edge_tuple_feasible p D.itemEquiv
    D.packingInstance_size_eq (D.graph.endpoint edge q.1) t hG
  have hcopy : anchorCopy p D.itemEquiv t =
      ⟨(anchorCopy p D.itemEquiv t).1, .inr w.key⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p D.itemEquiv t)]
    rw [w.anchor_eq]
  erw [InventoryCoverage.keyBaseline_selected_of_key p D.itemEquiv t _ w.key hcopy] at hkey
  erw [InventoryCoverage.rowBaseline_selected p D.itemEquiv t, w.row_eq] at hrow
  change Geometry.baseline D.graph.edges.length D.R (D.jobPosition w.row) = _ at hrow
  erw [InventoryCoverage.rowShort_selected p D.itemEquiv t, w.row_eq] at hshort
  change w.short ≠ true at hshort
  refine ⟨w, hf, Geometry.baseline_eq_iff.mp hkey, Geometry.baseline_eq_iff.mp hrow, ?_⟩
  exact Bool.eq_false_of_not_eq_true hshort

private theorem witness_key_item (p : Packing D.packingInstance b)
    (t : p.TableBin D.encodedSubclass) (w : EdgeTupleData p D.itemEquiv t) :
    D.itemEquiv (D.keyItem ⟨(anchorCopy p D.itemEquiv t).1, w.key⟩) =
      p.itemAtRole D.encodedSubclass t .anchor := by
  erw [← roleCopy_item p D.itemEquiv t .anchor]
  apply congrArg D.itemEquiv
  change (⟨.anchor, ⟨_, .inr w.key⟩⟩ : D.Item) =
    ⟨.anchor, anchorCopy p D.itemEquiv t⟩
  conv_rhs => rw [← Sigma.eta (anchorCopy p D.itemEquiv t), w.anchor_eq]

private theorem witness_global_item (p : Packing D.packingInstance b)
    (t : p.TableBin D.encodedSubclass) (w : EdgeTupleData p D.itemEquiv t) :
    D.itemEquiv (D.edgeResourceItem ((w.edge, w.permit), w.globalIndex)) =
      p.itemAtRole D.encodedSubclass t .«global» := by
  erw [← roleCopy_item p D.itemEquiv t .«global»]
  change D.itemEquiv ⟨.«global», ⟨.edge w.edge w.permit, w.globalIndex⟩⟩ =
    D.itemEquiv ⟨.«global», globalCopy p D.itemEquiv t⟩
  rw [w.global_eq]

theorem edgeLongTuplesAt_not_earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    t ∉ D.earlierGoodKeyTuples p edge.val edge.isLt.le := by
  obtain ⟨w, _, hkey, _, _⟩ := D.edgeLongTuplesAt_witness p edge q t ht
  intro hearlier
  have hmem := ((D.mem_earlierGoodKeyTuples p edge.val edge.isLt.le t).mp hearlier).2
  rw [← D.witness_key_item p t w, D.keyItem_mem_earlierKeyItems] at hmem
  simp only [hkey, Nat.lt_irrefl] at hmem

theorem edgeLongTuplesAt_global_not_used_earlier (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    p.itemAtRole D.encodedSubclass t .«global» ∉
      Coverage.roleItems p D.encodedSubclass
        (D.earlierGoodKeyTuples p edge.val edge.isLt.le) .«global» := by
  intro hi
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hi
  have hut : u = t := p.itemAtRole_injective D.encodedSubclass .«global» heq
  subst u
  exact D.edgeLongTuplesAt_not_earlierGoodKeyTuples p edge q t ht hu

theorem edgeLongTuplesAt_global_mem (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    p.itemAtRole D.encodedSubclass t .«global» ∈
      globalResources D.itemEquiv (.edge edge true) ∪
        D.remainingEarlierW p edge.val edge.isLt.le := by
  classical
  obtain ⟨w, hf, hkey, hrow, hshort⟩ := D.edgeLongTuplesAt_witness p edge q t ht
  have hresource := w.exact_long_resource hf (hrow.trans hkey.symm) hshort
  rcases hresource with hearlier | ⟨heq, hpermit⟩
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, D.edgeLongTuplesAt_global_not_used_earlier p edge q t ht⟩
    apply (D.mem_earlierWItems edge.val edge.isLt.le _).mpr
    refine ⟨((w.edge, w.permit), w.globalIndex), D.witness_global_item p t w, ?_⟩
    have hlt : w.edge < edge := by simpa only [hkey] using hearlier
    exact hlt
  · apply Finset.mem_union_left
    apply (selected_global_resource_iff p D.itemEquiv t (.edge edge true)).mpr
    rw [w.global_eq]
    have hedge : w.edge = edge := by simpa only [hkey] using heq
    simp only [hedge, hpermit]

theorem edgeLongTuples_global_subset (p : Packing D.packingInstance b)
    (edge : D.Edge) (J : Finset (Fin D.R)) :
    Coverage.roleItems p D.encodedSubclass (D.edgeLongTuples p edge J) .«global» ⊆
      globalResources D.itemEquiv (.edge edge true) ∪
        D.remainingEarlierW p edge.val edge.isLt.le := by
  classical
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp ht
  exact D.edgeLongTuplesAt_global_mem p edge q t hq

theorem edge_long_matches_capacity_oaiq082_oai {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (edge : D.Edge) (J : Finset (Fin D.R)) :
    (∑ side : Fin 2, ∑ rep ∈ J, (D.edgeLongTuplesAt p edge (side, rep)).card) ≤
      D.d * D.R + 3 * D.graph.n * lossAllowance c := by
  classical
  rw [← D.edgeLongTuples_card]
  have hbound := Finset.card_le_card (D.edgeLongTuples_global_subset p edge J)
  rw [Coverage.roleItems_card] at hbound
  refine hbound.trans ((Finset.card_union_le _ _).trans ?_)
  rw [globalResources_card]
  change D.d * D.R + (D.remainingEarlierW p edge.val edge.isLt.le).card ≤ _
  exact Nat.add_le_add_left (D.remainingEarlierW_card_le hk p hb edge.val edge.isLt.le) _

end InventoryData
end BinPackingGap

end

end OAI
end

theorem solution : type_of% @OAI.BinPackingGap.InventoryData.edge_long_matches_capacity_oaiq082_oai := @OAI.BinPackingGap.InventoryData.edge_long_matches_capacity_oaiq082_oai
