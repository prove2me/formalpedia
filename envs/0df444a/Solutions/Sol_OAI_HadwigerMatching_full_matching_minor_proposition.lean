-- Prove2me | solution 1 for OAI.HadwigerMatching.full_matching_minor_proposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:03:46.847053+00:00
-- url     : https://prove2.me/submissions/15f28da4-8b42-41c2-9b4f-2362f66ac2d9

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Definitions.Def_HadwigerMatching_Defs
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQ430Hc000

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_BasicMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HadwigerMatching

open scoped BigOperators

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Every member contributes exactly two vertices. -/
theorem IsTouchingMatching.sum_card_eq {M : Finset (Finset V)}
    (hM : IsTouchingMatching G M) :
    (∑ e ∈ M, e.card) = 2 * M.card := by
  rw [Finset.sum_const_nat (fun e he => (hM.1 e he).1)]
  exact Nat.mul_comm M.card 2

/-- Disjointness bounds twice the number of matching edges by the graph order. -/
theorem IsTouchingMatching.two_mul_card_le [Fintype V]
    {M : Finset (Finset V)} (hM : IsTouchingMatching G M) :
    2 * M.card ≤ Fintype.card V := by
  classical
  have hd : (M : Set (Finset V)).PairwiseDisjoint (fun e => e) := by
    intro e he f hf hne
    exact hM.2.1 e he f hf hne
  have hc : (M.biUnion (fun e => e)).card = 2 * M.card := by
    rw [Finset.card_biUnion hd]
    exact hM.sum_card_eq
  rw [← hc]
  exact Finset.card_le_univ _

/-- Touching matching cardinalities are bounded on a finite vertex type. -/
theorem connectedMatchingNumber_bddAbove [Fintype V] (G : SimpleGraph V) :
    BddAbove {n : ℕ | ∃ M : Finset (Finset V),
      IsTouchingMatching G M ∧ M.card = n} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨M, hM, rfl⟩
  have h : M.card + M.card ≤ Fintype.card V := by
    simpa only [two_mul] using hM.two_mul_card_le
  exact (Nat.le_add_right M.card M.card).trans h

/-- Every touching matching is bounded by the connected matching number. -/
theorem matching_card_le_number [Fintype V] {M : Finset (Finset V)}
    (hM : IsTouchingMatching G M) : M.card ≤ connectedMatchingNumber G := by
  exact le_csSup (connectedMatchingNumber_bddAbove G) ⟨M, hM, rfl⟩

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_BranchCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cardinal bounds for pairwise disjoint nonempty branch sets. -/
namespace HadwigerMatching
open scoped BigOperators

variable {V : Type*} {t : ℕ}

theorem sum_singleton_indicator (B : Fin t → Finset V) :
    (∑ i, if (B i).card = 1 then 1 else 0) = singletonBranchCount B := by
  simp [singletonBranchCount]

theorem sum_doubleton_indicator (B : Fin t → Finset V) :
    (∑ i, if (B i).card = 2 then 1 else 0) = doubletonBranchCount B := by
  simp [doubletonBranchCount]

/-- Disjoint branch sets occupy at most the ambient finite ground set. -/
theorem branch_card_sum_le [Fintype V] [DecidableEq V]
    (B : Fin t → Finset V) (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (∑ i, (B i).card) ≤ Fintype.card V := by
  have hd : (↑(Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint B :=
    fun i _ j _ hij => hdisj hij
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_univ _

/-- Every nonempty branch costs at least three, except for the exact deficits
of two for a singleton and one for a doubleton. -/
theorem branch_counting [Fintype V] [DecidableEq V]
    (B : Fin t → Finset V)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    3 * t ≤ Fintype.card V + 2 * singletonBranchCount B + doubletonBranchCount B := by
  have hpoint (i : Fin t) :
      3 ≤ (B i).card + 2 * (if (B i).card = 1 then 1 else 0) +
        (if (B i).card = 2 then 1 else 0) := by
    have hp : 0 < (B i).card := Finset.card_pos.mpr (hne i)
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hsum' : 3 * t ≤ (∑ i, (B i).card) +
      2 * singletonBranchCount B + doubletonBranchCount B := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_singleton_indicator, sum_doubleton_indicator, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_comm t 3] using hsum
  exact hsum'.trans (Nat.add_le_add_right
    (Nat.add_le_add_right (branch_card_sum_le B hdisj) _) _)

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.ListHadwiger_Basic
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

theorem cliqueMinor_order_le_card {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ Fintype.card V := by
  classical
  obtain ⟨B, hc, hd, _⟩ := h
  have hb : ∀ i, ∃ v, v ∈ B i := fun i => by
    obtain ⟨v⟩ := (hc i).nonempty
    exact ⟨v.val, v.property⟩
  choose v hv using hb
  have hi : Function.Injective v := by
    intro i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hd i j hn) (hv i) (by
      rw [hij]
      exact hv j)
  simpa using Fintype.card_le_of_injective v hi

theorem cliqueMinor_zero {V : Type} (G : SimpleGraph V) : HasCliqueMinor G 0 := by
  refine ⟨Fin.elim0, ?_, ?_, ?_⟩
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i

theorem hadwiger_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove {t : ℕ | HasCliqueMinor G t} :=
  ⟨Fintype.card V, fun _ h => cliqueMinor_order_le_card h⟩

theorem hasCliqueMinor_hadwigerNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    HasCliqueMinor G (hadwigerNumber G) := by
  exact Nat.sSup_mem ⟨0, cliqueMinor_zero G⟩ (hadwiger_bddAbove G)

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_BranchGeometry
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clique geometry of singleton and doubleton branches and finite clique-minor models. -/
namespace HadwigerMatching

variable {V : Type} {G : SimpleGraph V}

/-- A connected induced graph on precisely two vertices contains their edge. -/
theorem connected_card_two_isClique [DecidableEq V] (S : Finset V)
    (hS : S.card = 2) (hc : (G.induce (S : Set V)).Connected) :
    G.IsClique (S : Set V) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  have hedge : G.Adj a b := by
    let a' : ({a, b} : Finset V) := ⟨a, by simp⟩
    let b' : ({a, b} : Finset V) := ⟨b, by simp⟩
    have hne : a' ≠ b' := by
      intro h
      exact hab (congrArg Subtype.val h)
    obtain ⟨p⟩ := hc.preconnected a' b'
    have hadj := p.adj_snd (p.not_nil_of_ne hne)
    have hsnd : (p.snd : V) = a ∨ (p.snd : V) = b := by
      simpa using p.snd.property
    rcases hsnd with hsnd | hsnd
    · change G.Adj a (p.snd : V) at hadj
      rw [hsnd] at hadj
      exact (G.irrefl hadj).elim
    · simpa [a', hsnd] using hadj
  intro x hx y hy hxy
  have hx' : x = a ∨ x = b := by simpa using hx
  have hy' : y = a ∨ y = b := by simpa using hy
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact (hxy rfl).elim
  · exact hedge
  · exact hedge.symm
  · exact (hxy rfl).elim

/-- On a finite vertex type, clique-minor branches can be represented by finite sets. -/
theorem finite_branch_model [Fintype V] {t : ℕ}
    (h : LinearListHadwiger.HasCliqueMinor G t) :
    ∃ B : Fin t → Finset V,
      (∀ i, (G.induce (B i : Set V)).Connected) ∧
      (∀ i, (B i).Nonempty) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) := by
  classical
  obtain ⟨A, hconn, hdisj, htouch⟩ := h
  let B : Fin t → Finset V := fun i => (A i).toFinset
  have hcoe (i : Fin t) : (B i : Set V) = A i := by simp [B]
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hcoe]
    exact hconn i
  · intro i
    obtain ⟨v⟩ := (hconn i).nonempty
    exact ⟨v.val, Set.mem_toFinset.mpr v.property⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact Set.disjoint_left.mp (hdisj i j hij)
      (by simpa [B] using hvi) (by simpa [B] using hvj)
  · intro i j hij
    obtain ⟨v, hv, w, hw, hvw⟩ := htouch i j hij
    exact ⟨v, by simpa [B] using hv, w, by simpa [B] using hw, hvw⟩

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_ChromaticBound
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A chromatic lower bound for finite graphs with independence number at most two. -/

namespace HadwigerMatching

open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Every color fiber is an independent vertex set, so a coloring by `k`
colors can cover at most `2*k` vertices under the stated independence bound. -/
theorem card_le_twice_of_coloring {k : ℕ} (C : G.Coloring (Fin k))
    (hα : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ 2) :
    Fintype.card V ≤ 2 * k := by
  classical
  let fiber : Fin k → Finset V := fun c => Finset.univ.filter (fun v => C v = c)
  have hfiber (c : Fin k) : (fiber c).card ≤ 2 := by
    apply hα
    intro v hv w hw _ hadj
    exact C.valid hadj ((Finset.mem_filter.mp hv).2.trans
      (Finset.mem_filter.mp hw).2.symm)
  have hcount : ∑ c : Fin k, (fiber c).card = Fintype.card V := by
    simp only [fiber, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  calc
    Fintype.card V = ∑ c : Fin k, (fiber c).card := hcount.symm
    _ ≤ ∑ _c : Fin k, 2 := Finset.sum_le_sum (fun c _ => hfiber c)
    _ = 2 * k := by simp [Nat.mul_comm]

/-- A finite graph has finite chromatic number; an optimal coloring
then proves the lower bound, including the empty vertex type. -/
theorem card_le_twice_chromaticNumber
    (hα : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ 2) :
    Fintype.card V ≤ 2 * G.chromaticNumber.toNat := by
  have hfinite : G.chromaticNumber ≠ ⊤ := by
    intro htop
    have h := G.chromaticNumber_le_card
    rw [htop] at h
    simp at h
  obtain ⟨C⟩ := G.colorable_of_chromaticNumber_ne_top hfinite
  exact card_le_twice_of_coloring G C hα

/-- A graph with independence number at most two needs at least half as many
colors as vertices. -/
theorem card_le_twice_chromaticNumber_of_indepNum (hα : G.indepNum ≤ 2) :
    Fintype.card V ≤ 2 * G.chromaticNumber.toNat := by
  apply card_le_twice_chromaticNumber G
  intro S hS
  exact hS.card_le_indepNum.trans hα

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_FinitePairing
attribute [-instance] _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HadwigerMatching

/-- A finite set admits pairwise disjoint two-element subsets covering all but at most
one of its elements, without requiring the ambient type to be finite. -/
theorem exists_finite_pairing {V : Type*} (S : Finset V) :
    ∃ P : Finset (Finset V),
      (∀ A ∈ P, A.card = 2 ∧ A ⊆ S) ∧
      (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      2 * P.card ≤ S.card ∧ S.card ≤ 2 * P.card + 1 := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hsmall : S.card ≤ 1
    · exact ⟨∅, by simp, by simp, by simp, by simpa using hsmall⟩
    have hpos : 0 < S.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    have hca := Finset.card_erase_add_one ha
    have hpos' : 0 < (S.erase a).card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos'
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hbS : b ∈ S := (Finset.mem_erase.mp hb).2
    let R := (S.erase a).erase b
    have hR : R ⊂ S :=
      Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) (Finset.erase_ssubset ha)
    obtain ⟨P, hP, hdisj, hlo, hhi⟩ := ih R hR
    have hcr : R.card + 2 = S.card := by
      have hcb := Finset.card_erase_add_one hb
      dsimp [R]
      omega
    have hRsub : R ⊆ S := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have haR : a ∉ R := by simp [R]
    have hbR : b ∉ R := by simp [R]
    have hpair : ({a, b} : Finset V).card = 2 := by simp [Ne.symm hba]
    have hpairsub : ({a, b} : Finset V) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · have hxb := Finset.mem_singleton.mp hx
        subst x
        exact hbS
    have hnew : ({a, b} : Finset V) ∉ P := by
      intro hp
      exact haR ((hP _ hp).2 (by simp))
    have hpairdisj : ∀ A ∈ P, Disjoint ({a, b} : Finset V) A := by
      intro A hA
      apply Finset.disjoint_left.mpr
      intro x hx hxA
      have hxR := (hP A hA).2 hxA
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haR hxR
      · have hxb := Finset.mem_singleton.mp hx
        subst x
        exact hbR hxR
    refine ⟨insert {a, b} P, ?_, ?_, ?_, ?_⟩
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact ⟨hpair, hpairsub⟩
      · exact ⟨(hP A hA).1, fun x hx => hRsub ((hP A hA).2 hx)⟩
    · intro A hA B hB hne
      rcases Finset.mem_insert.mp hA with rfl | hA
      · rcases Finset.mem_insert.mp hB with rfl | hB
        · exact (hne rfl).elim
        · exact hpairdisj B hB
      · rcases Finset.mem_insert.mp hB with rfl | hB
        · exact (hpairdisj A hA).symm
        · exact hdisj A hA B hB hne
    · rw [Finset.card_insert_of_notMem hnew]
      omega
    · rw [Finset.card_insert_of_notMem hnew]
      omega

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_PairingExtension
attribute [-instance] _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HadwigerMatching

/-- Disjoint pairs from a clique extend a touching matching when every clique vertex
is adjacent to a vertex in each existing matching edge. -/
theorem extend_matching_by_clique_pairs {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (E : Finset (Finset V)) (S : Finset V)
    (hE : IsTouchingMatching G E) (hS : G.IsClique (S : Set V))
    (hdisj : ∀ e ∈ E, Disjoint e S)
    (htouch : ∀ v ∈ S, ∀ e ∈ E, ∃ w ∈ e, G.Adj v w) :
    ∃ P : Finset (Finset V), IsTouchingMatching G (E ∪ P) ∧
      (E ∪ P).card = E.card + P.card ∧ S.card ≤ 2 * P.card + 1 := by
  classical
  obtain ⟨P, hP, hPP, _hlo, hhi⟩ := exists_finite_pairing S
  have hnonempty : ∀ p ∈ P, p.Nonempty := by
    intro p hp
    exact Finset.card_pos.mp (by rw [(hP p hp).1]; decide)
  have hEP : ∀ e ∈ E, ∀ p ∈ P, Disjoint e p := by
    intro e he p hp
    apply Finset.disjoint_left.mpr
    intro x hxe hxp
    exact Finset.disjoint_left.mp (hdisj e he) hxe ((hP p hp).2 hxp)
  have hfamily : Disjoint E P := by
    apply Finset.disjoint_left.mpr
    intro e he hp
    obtain ⟨v, hv⟩ := hnonempty e hp
    exact Finset.disjoint_left.mp (hEP e he e hp) hv hv
  have hclique : ∀ p ∈ P, G.IsClique (p : Set V) := by
    intro p hp v hv w hw hne
    exact hS ((hP p hp).2 hv) ((hP p hp).2 hw) hne
  have hPT : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ∃ v ∈ p, ∃ w ∈ q, G.Adj v w := by
    intro p hp q hq hne
    obtain ⟨v, hv⟩ := hnonempty p hp
    obtain ⟨w, hw⟩ := hnonempty q hq
    have hvw : v ≠ w := by
      intro heq
      subst w
      exact Finset.disjoint_left.mp (hPP p hp q hq hne) hv hw
    exact ⟨v, hv, w, hw, hS ((hP p hp).2 hv) ((hP q hq).2 hw) hvw⟩
  have hPEtouch : ∀ p ∈ P, ∀ e ∈ E,
      ∃ v ∈ p, ∃ w ∈ e, G.Adj v w := by
    intro p hp e he
    obtain ⟨v, hv⟩ := hnonempty p hp
    obtain ⟨w, hw, hvw⟩ := htouch v ((hP p hp).2 hv) e he
    exact ⟨v, hv, w, hw, hvw⟩
  refine ⟨P, ?_, Finset.card_union_of_disjoint hfamily, hhi⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hE.1 e he
    · exact ⟨(hP e he).1, hclique e he⟩
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact hE.2.1 e he f hf hne
    · exact hEP e he f hf
    · exact (hEP f hf e he).symm
    · exact hPP e he f hf hne
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact hE.2.2 e he f hf hne
    · obtain ⟨v, hv, w, hw, hvw⟩ := hPEtouch f hf e he
      exact ⟨w, hw, v, hv, hvw.symm⟩
    · exact hPEtouch e he f hf
    · exact hPT e he f hf hne

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_SmallBranches
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cliques and touching matchings formed by singleton and doubleton branches. -/
namespace HadwigerMatching
open scoped BigOperators
variable {V : Type*} [DecidableEq V] {t : ℕ}

theorem mem_singletonVertices (B : Fin t → Finset V) (v : V) :
    v ∈ singletonVertices B ↔ ∃ i, (B i).card = 1 ∧ v ∈ B i := by
  simp [singletonVertices]

theorem mem_twoVertexBranches (B : Fin t → Finset V) (e : Finset V) :
    e ∈ twoVertexBranches B ↔ ∃ i, (B i).card = 2 ∧ B i = e := by
  simp [twoVertexBranches]

omit [DecidableEq V] in
/-- Nonemptiness is essential: distinct empty branches would not be injective. -/
theorem branches_injective (B : Fin t → Finset V)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Function.Injective B := by
  intro i j he
  by_contra hij
  obtain ⟨v, hv⟩ := hne i
  exact Finset.disjoint_left.mp (hdisj hij) hv (he ▸ hv)

theorem card_singletonVertices (B : Fin t → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (singletonVertices B).card = singletonBranchCount B := by
  unfold singletonVertices singletonBranchCount
  rw [Finset.card_biUnion (fun i _ j _ hij => hdisj hij)]
  calc
    (∑ i ∈ Finset.univ.filter (fun i => (B i).card = 1), (B i).card) =
        ∑ i ∈ Finset.univ.filter (fun i => (B i).card = 1), 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    _ = _ := by simp

theorem card_twoVertexBranches (B : Fin t → Finset V)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (twoVertexBranches B).card = doubletonBranchCount B := by
  unfold twoVertexBranches doubletonBranchCount
  exact Finset.card_image_of_injective _ (branches_injective B hne hdisj)

omit [DecidableEq V] in
theorem singleton_branch_eq (B : Fin t → Finset V) {i : Fin t} {v : V}
    (hi : (B i).card = 1) (hv : v ∈ B i) : B i = {v} := by
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hi
  have hvw : v = w := by simpa [hw] using hv
  simpa [hvw] using hw

theorem singletonVertices_isClique (G : SimpleGraph V) (B : Fin t → Finset V)
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) :
    G.IsClique (singletonVertices B : Set V) := by
  intro v hv w hw hvw
  obtain ⟨i, hi, hvi⟩ := (mem_singletonVertices B v).mp hv
  obtain ⟨j, hj, hwj⟩ := (mem_singletonVertices B w).mp hw
  have hBi := singleton_branch_eq B hi hvi
  have hBj := singleton_branch_eq B hj hwj
  have hij : i ≠ j := by
    intro he
    have hmem : v ∈ B j := he ▸ hvi
    have hvw' : v = w := by simpa [hBj] using hmem
    exact hvw hvw'
  obtain ⟨x, hx, y, hy, hxy⟩ := htouch i j hij
  have hxv : x = v := by simpa [hBi] using hx
  have hyw : y = w := by simpa [hBj] using hy
  simpa [hxv, hyw] using hxy

theorem twoVertexBranches_isTouchingMatching (G : SimpleGraph V)
    (B : Fin t → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)
    (hclique : ∀ i, (B i).card = 2 → G.IsClique (B i : Set V)) :
    IsTouchingMatching G (twoVertexBranches B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi, rfl⟩ := (mem_twoVertexBranches B e).mp he
    exact ⟨hi, hclique i hi⟩
  · intro e he f hf hef
    obtain ⟨i, _, rfl⟩ := (mem_twoVertexBranches B e).mp he
    obtain ⟨j, _, rfl⟩ := (mem_twoVertexBranches B f).mp hf
    exact hdisj (fun hij => hef (congrArg B hij))
  · intro e he f hf hef
    obtain ⟨i, _, rfl⟩ := (mem_twoVertexBranches B e).mp he
    obtain ⟨j, _, rfl⟩ := (mem_twoVertexBranches B f).mp hf
    exact htouch i j (fun hij => hef (congrArg B hij))

theorem twoVertexBranches_disjoint_singletonVertices (B : Fin t → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    {e : Finset V} (he : e ∈ twoVertexBranches B) :
    Disjoint e (singletonVertices B) := by
  obtain ⟨i, hi, rfl⟩ := (mem_twoVertexBranches B e).mp he
  apply Finset.disjoint_left.mpr
  intro v hvi hv
  obtain ⟨j, hj, hvj⟩ := (mem_singletonVertices B v).mp hv
  have hij : i ≠ j := by
    intro heq
    have : (2 : ℕ) = 1 := hi.symm.trans ((congrArg (fun k => (B k).card) heq).trans hj)
    exact (by decide : (2 : ℕ) ≠ 1) this
  exact Finset.disjoint_left.mp (hdisj hij) hvi hvj

theorem singletonVertices_touch_twoVertexBranches (G : SimpleGraph V)
    (B : Fin t → Finset V)
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)
    {v : V} (hv : v ∈ singletonVertices B)
    {e : Finset V} (he : e ∈ twoVertexBranches B) :
    ∃ w ∈ e, G.Adj v w := by
  obtain ⟨i, hi, hvi⟩ := (mem_singletonVertices B v).mp hv
  obtain ⟨j, hj, rfl⟩ := (mem_twoVertexBranches B e).mp he
  have hij : i ≠ j := by
    intro heq
    have : (1 : ℕ) = 2 := hi.symm.trans ((congrArg (fun k => (B k).card) heq).trans hj)
    exact (by decide : (1 : ℕ) ≠ 2) this
  obtain ⟨x, hx, w, hw, hxw⟩ := htouch i j hij
  have hxv : x = v := by simpa [singleton_branch_eq B hi hvi] using hx
  exact ⟨w, hw, hxv ▸ hxw⟩

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_MinorBound
attribute [-instance] _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral Hadwiger bound from pairwise touching matchings.

The small-branch counting argument is Proposition `matching-minor` of
*A counterexample to Hadwiger's conjecture*, following the connected-matching
approach of Cambie.
-/

namespace HadwigerMatching

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- The singleton and doubleton deficits of an actual clique-minor model are
controlled by a touching matching constructed from those very branches. -/
theorem small_branch_deficit_le {t : ℕ} (B : Fin t → Finset V)
    (hconn : ∀ i, (G.induce (B i : Set V)).Connected)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) :
    2 * singletonBranchCount B + doubletonBranchCount B ≤
      4 * connectedMatchingNumber G + 2 := by
  classical
  have hE := twoVertexBranches_isTouchingMatching G B hdisj htouch
    (fun i hi => connected_card_two_isClique (B i) hi (hconn i))
  obtain ⟨P, hP, hcard, hcover⟩ := extend_matching_by_clique_pairs G
    (twoVertexBranches B) (singletonVertices B) hE
    (singletonVertices_isClique G B htouch)
    (fun _ he => twoVertexBranches_disjoint_singletonVertices B hdisj he)
    (fun _ hv _ he => singletonVertices_touch_twoVertexBranches G B htouch hv he)
  have hbound := matching_card_le_number hP
  rw [hcard, card_twoVertexBranches B hne hdisj] at hbound
  rw [card_singletonVertices B hdisj] at hcover
  omega

/-- Every clique minor satisfies the integral matching bound. -/
theorem clique_minor_matching_bound {t : ℕ}
    (h : LinearListHadwiger.HasCliqueMinor G t) :
    3 * t ≤ Fintype.card V + 4 * connectedMatchingNumber G + 2 := by
  classical
  obtain ⟨B, hconn, hne, hdisj, htouch⟩ := finite_branch_model h
  have hcount := branch_counting B hne hdisj
  have hsmall := small_branch_deficit_le B hconn hne hdisj htouch
  omega

/-- The maximum is attained by an actual clique-minor branch model. This proves
the bound for the literal Hadwiger number, including the empty graph. -/
theorem hadwiger_matching_bound (G : SimpleGraph V) :
    3 * LinearListHadwiger.hadwigerNumber G ≤
      Fintype.card V + 4 * connectedMatchingNumber G + 2 :=
  clique_minor_matching_bound (LinearListHadwiger.hasCliqueMinor_hadwigerNumber G)

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HadwigerMatching

/-- The matching–minor proposition: the Hadwiger bound and its chromatic
consequence when the independence and touching-matching numbers are small. -/
theorem full_matching_minor_proposition_oai
    (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    let m : ℕ := Fintype.card V
    let h : ℕ := LinearListHadwiger.hadwigerNumber G
    let c : ℕ := HadwigerMatching.connectedMatchingNumber G
    (h : ℚ) ≤ ((m : ℚ) + 4 * (c : ℚ) + 2) / 3 ∧
      (G.indepNum ≤ 2 →
        (c : ℚ) < (m : ℚ) / 100 →
        5 ≤ m →
        (h : ℚ) < 26 * (m : ℚ) / 75 + 2 / 3 ∧
        26 * (m : ℚ) / 75 + 2 / 3 < (m : ℚ) / 2 ∧
        (m : ℚ) / 2 ≤ (G.chromaticNumber.toNat : ℚ)) := by
  dsimp only
  have hn := hadwiger_matching_bound G
  have hq : 3 * (LinearListHadwiger.hadwigerNumber G : ℚ) ≤
      (Fintype.card V : ℚ) + 4 * (connectedMatchingNumber G : ℚ) + 2 := by
    exact_mod_cast hn
  refine ⟨by linarith, ?_⟩
  intro hα hc hm
  have hm' : (5 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hm
  have hnχ := card_le_twice_chromaticNumber_of_indepNum G hα
  have hχ : (Fintype.card V : ℚ) ≤ 2 * (G.chromaticNumber.toNat : ℚ) := by
    exact_mod_cast hnχ
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end HadwigerMatching

end OAI
end

theorem solution : type_of% @OAI.HadwigerMatching.full_matching_minor_proposition_oai := @OAI.HadwigerMatching.full_matching_minor_proposition_oai
