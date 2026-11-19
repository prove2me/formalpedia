-- Prove2me | solution 1 for OAI.UniversalTensorSquare.balance_kronecker_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:12:43.01962+00:00
-- url     : https://prove2.me/submissions/448d12a4-2895-4008-8235-2b03c0f83176

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_Saxl_Balance_WordPacking_kronecker_pos
import Theorems.Thm_OAI_Saxl_Balance_balancePacking
import Theorems.Thm_OAI_UniversalTensorSquare_balance_dominance
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_rowLens

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

lemma columnShape_rowLen (rs : List ℕ) (i : ℕ) :
    (columnShape rs).rowLen i = rs.countP (fun h => i < h) := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_rowLen e hr i

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma sum_wordContent {n d : ℕ} (w : Fin n → Fin d) :
    ∑ j, wordContent w j = n := by
  classical
  simp only [wordContent,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

namespace Balance
open FlagColumns Columns

lemma WordPacking.total {rs ps : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps d A label marks) : ps.sum = rs.sum := by
  calc
    ps.sum = ∑ j, ps.get j := by rw [← List.sum_ofFn, List.ofFn_get]
    _ = ∑ j, wordContent P.word j := Finset.sum_congr rfl (fun j _ => (P.counts j).symm)
    _ = rs.sum := sum_wordContent P.word

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_PartWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Part Words. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma balancedParts_part {n k p : ℕ} (hp : p ∈ balancedParts n k) :
    n/k ≤ p ∧ p ≤ (n+k-1)/k := by
  simp only [balancedParts, List.mem_ofFn] at hp
  obtain ⟨j,rfl⟩ := hp
  have hk : 0 < k := Nat.zero_lt_of_lt j.isLt
  have hn : n = k*(n/k) + n%k := (Nat.div_add_mod n k).symm
  have hr := Nat.mod_lt n hk
  constructor
  · omega
  · split_ifs with h
    · apply (Nat.le_div_iff_mul_le hk).mpr
      have ht : n%k ≥ 1 := by omega
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm]
      omega
    · apply (Nat.le_div_iff_mul_le hk).mpr
      simp only [Nat.add_zero]
      rw [Nat.mul_comm]
      omega

lemma balancedParts_pos {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∀ p ∈ balancedParts n k, 0 < p := by
  intro p hp
  have h := (balancedParts_part hp).1
  have hn : 1 ≤ n/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa)
  omega

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Blocks. -/

section

noncomputable section
namespace Saxl.Balance

lemma bigParts_length {q δ : ℕ} (hδ : δ ≤ 1) : (bigParts q δ).length = 5-δ := by
  simp only [bigParts,List.length_append,balancedParts_length,oneIf]
  split_ifs <;> simp_all <;> omega

lemma shortParts_length {m τ : ℕ} (hτ : τ ≤ 1) : (shortParts m τ).length = 1+τ := by
  simp only [shortParts]
  split_ifs <;> simp_all
  omega

lemma oneIf_length {x ε : ℕ} (hε : ε ≤ 1) : (oneIf x ε).length = ε := by
  unfold oneIf
  split_ifs <;> simp_all
  omega

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_PairRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Run. -/

section

noncomputable section
namespace Saxl.Balance

lemma pairColumns_succ (a m : ℕ) :
    pairColumns a (m+1) = pairColumns a m ++ [a+2*m+1,a+2*m] := by
  simp [pairColumns,List.range_succ]

lemma pairParts_succ (a m : ℕ) :
    pairParts a (m+1) = pairParts a m ++ balancedParts (2*(a+2*m)+1) 4 := by
  simp [pairParts,List.range_succ]

lemma pairColumns_perm (a m : ℕ) : (pairColumns a m).Perm (List.range' a (2*m)) := by
  induction m with
  | zero => simp [pairColumns]
  | succ m ih =>
    rw [pairColumns_succ]
    have hpair : [a+2*m+1,a+2*m].Perm (List.range' (a+2*m) 2) := by
      simpa [List.range'] using List.Perm.swap (a+2*m) (a+2*m+1) []
    have h := ih.append hpair
    rw [List.range'_append_1] at h
    simpa only [Nat.mul_add,Nat.mul_one] using h

lemma pairParts_length (a m : ℕ) : (pairParts a m).length = 4*m := by
  induction m with
  | zero => simp [pairParts]
  | succ m ih => rw [pairParts_succ,List.length_append,ih,balancedParts_length]; omega

lemma pairParts_positive {a m : ℕ} (ha : 2 ≤ a) : ∀ p ∈ pairParts a m, 0 < p := by
  intro p hp
  obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
  exact balancedParts_pos (by decide) (by omega) p hp

lemma pairParts_bound {a m p : ℕ} (_ha : 2 ≤ a) (hp : p ∈ pairParts a m) :
    p < a+2*m := by
  obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
  have hj := List.mem_range.mp hj
  have hb := (balancedParts_part hp).2
  omega

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Assembly. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

lemma balanceParts_length {M b δ τ ε m : ℕ}
    (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1) (heq : M = 4+τ+ε+2*m) :
    2*M-5 ≤ (balanceParts M b δ τ ε m).length := by
  rw [balanceParts,List.length_append,List.length_append,List.length_append,
    bigParts_length hδ,shortParts_length hτ,pairParts_length,oneIf_length hε]
  omega

lemma oneIf_mem {x ε p : ℕ} (hp : p ∈ oneIf x ε) : p = x := by
  unfold oneIf at hp
  split_ifs at hp
  · simp at hp
  · exact List.mem_singleton.mp hp

lemma balanceParts_positive {M b δ τ ε m : ℕ} (hM : 4 ≤ M) :
    ∀ p ∈ balanceParts M b δ τ ε m, 0 < p := by
  intro p hp
  simp only [balanceParts,List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact balancedParts_pos (by decide) (by omega) p hp
    · have := oneIf_mem hp; omega
  · unfold shortParts at hp
    split_ifs at hp
    · have := List.mem_singleton.mp hp; omega
    · exact balancedParts_pos (by decide) (by omega) p hp
  · exact pairParts_positive (by omega) p hp
  · have := oneIf_mem hp; omega

lemma balanceParts_bound {M b δ τ ε m p : ℕ}
    (hM : 4 ≤ M) (hb : b ≤ M-2) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (heq : M = 4+τ+ε+2*m) (hsmall : τ = 0 → 2*(b+1) ≤ M)
    (hp : p ∈ balanceParts M b δ τ ε m) : p ≤ M+1 := by
  simp only [balanceParts,List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases List.mem_append.mp hp with hp | hp
    · have hh := (balancedParts_part hp).2
      omega
    · have := oneIf_mem hp; omega
  · unfold shortParts at hp
    split_ifs at hp with ht
    · have := List.mem_singleton.mp hp
      have := hsmall ht
      omega
    · have hh := (balancedParts_part hp).2
      omega
  · have := pairParts_bound (by omega : 2 ≤ 3+τ+ε) hp
    omega
  · have := oneIf_mem hp; omega

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CandidateColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Columns. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma oneIf_range {x ε : ℕ} (hε : ε ≤ 1) : oneIf x ε = List.range' x ε := by
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl <;> simp [oneIf,List.range']

lemma balanceColumns_perm {M b δ τ ε m : ℕ}
    (hM : 4 ≤ M) (hτ : τ ≤ 1) (hε : ε ≤ 1) (heq : M = 4+τ+ε+2*m) :
    (balanceColumns M b δ τ ε m).Perm (candidate M b δ).transpose.rowLens := by
  rw [candidate_transpose,candidate_rowLens (by omega)]
  have hrun : oneIf 3 τ ++ oneIf (3+τ) ε ++ List.range' (3+τ+ε) (2*m) =
      List.range' 3 (M-4) := by
    rw [oneIf_range hτ,oneIf_range hε,List.range'_append_1, Nat.add_assoc 3 τ ε,List.range'_append_1]
    congr 1
    omega
  apply List.perm_iff_count.mpr
  intro x
  simp only [balanceColumns,bigColumns,shortColumns,List.count_append,List.count_reverse,
    (pairColumns_perm (3+τ+ε) m).count_eq,show M-1+b+1+δ = M+b+δ by omega]
  have hh := congrArg (List.count x) hrun
  simp only [List.count_append] at hh
  omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceFour
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Four. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

lemma balanceParts_shape_bounds {M b δ τ ε m : ℕ}
    (hM : 9 ≤ M) (hb : b ≤ M-2) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (heq : M = 4+τ+ε+2*m) (hsmall : τ = 0 → 2*(b+1) ≤ M) :
    let θ := (columnShape (balanceParts M b δ τ ε m)).transpose
    2*M-5 ≤ θ.colLen 0 ∧ θ.rowLen 0 ≤ M+1 ∧ 2 ≤ θ.rowLen 3 := by
  let ps := balanceParts M b δ τ ε m
  let θ := (columnShape ps).transpose
  have hp := balanceParts_positive (M := M) (b := b) (δ := δ) (τ := τ) (ε := ε) (m := m) (by omega)
  have hperm := columnShape_rows_permutation ps hp
  have hlen : ps.length = θ.colLen 0 := by
    simpa only [YoungDiagram.length_rowLens] using hperm.length_eq
  have hlower : 2*M-5 ≤ θ.colLen 0 := hlen ▸ balanceParts_length hδ hτ hε heq
  refine ⟨hlower,?_,?_⟩
  · have hzero : 0 < θ.rowLens.length := by rw [YoungDiagram.length_rowLens]; omega
    have hh : θ.rowLen 0 ∈ ps := by
      apply hperm.mem_iff.mpr
      rw [← YoungDiagram.get_rowLens (h := hzero)]
      exact List.getElem_mem hzero
    exact balanceParts_bound (by omega) hb hδ hτ hε heq hsmall hh
  · rw [YoungDiagram.rowLen_transpose]
    change 2 ≤ (columnShape ps).colLen 3
    suffices h : 3 < (columnShape ps).rowLen 1 from
      YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    rw [columnShape_rowLen]
    have hfour : List.countP (fun p => decide (1 < p))
        (balancedParts (2*(M-1+b)+1+3*δ) 4) = 4 := by
      rw [List.countP_eq_length.mpr ?_,balancedParts_length]
      intro p hp
      simp only [decide_eq_true_eq]
      have hh := (balancedParts_part hp).1
      omega
    dsimp only [ps,balanceParts,bigParts]
    simp only [List.countP_append,hfour]
    omega

theorem balance_kronecker_pos_oai {n M b δ : ℕ} (hM : 9 ≤ M)
    (hb : b ≤ M-2) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (μ : YoungDiagram) (s : Tableau n μ)
    (hμ : colPrefix μ 4 ≤ 2*M-2) : 0 < kronecker t t s := by
  let τ := if 2*(b+1) ≤ M then 0 else 1
  let ε := (M-4-τ)%2
  let m := (M-4-τ)/2
  have hτ : τ ≤ 1 := by dsimp [τ]; split_ifs <;> omega
  have hε : ε ≤ 1 := by dsimp [ε]; omega
  have heq : M = 4+τ+ε+2*m := by dsimp [ε,m]; omega
  have hsmall : τ = 0 → 2*(b+1) ≤ M := by
    intro ht
    by_contra h
    have hh : τ = 1 := ite_eq_right h
    omega
  have hshort : τ ≠ 0 → 1 ≤ b := by
    intro ht
    have hn : ¬ 2*(b+1) ≤ M := by
      intro h
      exact ht (ite_eq_left h)
    omega
  have hheight : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ (by omega)]
    simp [candidateLengths]
  have hpack := balancePacking (by omega) hδ hτ hε heq hshort
  rw [← hheight] at hpack
  obtain ⟨A,label,marks,hordered,⟨P⟩⟩ := hpack
  let rs := balanceColumns M b δ τ ε m
  let ps := balanceParts M b δ τ ε m
  have hperm := balanceColumns_perm (b := b) (δ := δ) (by omega) hτ hε heq
  obtain ⟨e,hr,hc⟩ := place_columns (candidate M b δ) hperm
  have hdegree : rs.sum = n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (((enumerate rs).trans e).trans t.symm)
  subst n
  let a := (enumerate rs).trans e
  have hcand : (candidate M b δ).card = rs.sum := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr a).symm
  have htarget : μ.card = rs.sum := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr s).symm
  have hparts : μ.card = (columnShape ps).transpose.card := by
    rw [htarget,transpose_card,columnShape_card]
    exact P.total.symm
  have hn : (staircase M).card ≤ μ.card := by
    rw [htarget,← hcand,candidate_card _ _ _ (by omega)]
    omega
  obtain ⟨hcount,hmax,hfour⟩ := balanceParts_shape_bounds hM hb hδ hτ hε heq hsmall
  have hdom := balance_dominance M hM μ (columnShape ps).transpose hparts hn hμ hcount hmax hfour
  have hpos := P.kronecker_pos a s (standard_placed_self e hr hc)
    (balanceParts_positive (by omega)) hordered hdom
  unfold kronecker spechtRep Specht at hpos ⊢
  rw [spechtSub_tableau_independent a t] at hpos
  exact hpos

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.balance_kronecker_pos_oai := @OAI.UniversalTensorSquare.balance_kronecker_pos_oai
