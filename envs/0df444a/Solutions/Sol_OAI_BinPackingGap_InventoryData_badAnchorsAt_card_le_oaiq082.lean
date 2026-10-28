-- Prove2me | solution 1 for OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le_oaiq082
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:01:24.256656+00:00
-- url     : https://prove2.me/submissions/22890b44-c2a9-4ccf-8e2a-2c6c9ed723ab

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C015

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
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
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
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.InventoryData.roleCopiesFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
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
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.InventoryData.roleCopiesFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace Coverage

variable {I : Instance} {b n : ℕ}

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
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
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
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
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
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
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

end Coverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryPrefixConservation
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
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

theorem badAnchorsAt_card_le_oaiq082_oai {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (v : D.Vertex) :
    (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel v).card ≤
      3 * lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    Coverage.badAnchorsAt_card_le p D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)
      D.roleLabelData_anchor_row_count D.roleLabelData_anchor_local_count v

end InventoryData
end BinPackingGap

end

end OAI
end

theorem solution : type_of% @OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le_oaiq082_oai := @OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le_oaiq082_oai
