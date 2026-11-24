-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s039PackingInput_of_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:15.509986+00:00
-- url     : https://prove2.me/submissions/6a1a95b9-f788-459b-b318-a9e60865802f

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_s039_signature_of_arithmetic
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_card_two_or_three
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_disjoint_of_ne
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_s039AllBlocks_pairwiseDisjoint
public import Theorems.Thm_InverseZeroSum_Candidate3_representativeSet_card_of_pairwise
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_card_le_sixteen_of_eta17
public import Theorems.Thm_InverseZeroSum_Candidate3_card_le_eighteen_of_threeTerm19
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    (h19 : ThreeTerm19Input) (hEta : Eta17Input) :
    S039PackingInput := by
  classical
  intro S hAvoid
  let P : Finset (Finset (Fin 24)) := s039AllBlocks S
  let P3 : Finset (Finset (Fin 24)) := P.filter (fun B => B.card = 3)
  let P2 : Finset (Finset (Fin 24)) := P.filter (fun B => B.card ≠ 3)
  let l : ℕ := P3.card
  let t : ℕ := P2.card
  let s : ℕ := l + t
  let U : Finset (Fin 24) := P.biUnion id
  let r : ℕ := (Finset.univ \ U).card

  have hPShort : ∀ B ∈ P, ShortZero S B := by
    intro B hB
    simpa [P] using hB

  have hPCardSplit : l + t = P.card := by
    have h :=
      Finset.sum_filter_add_sum_filter_not P
        (fun B : Finset (Fin 24) => B.card = 3) (fun _ => (1 : ℕ))
    simpa [l, t, P3, P2] using h

  have hPCard : P.card = s := by
    dsimp [s]
    omega

  have hP3Short : ∀ B ∈ P3, ShortZero S B := by
    intro B hB
    exact hPShort B (Finset.mem_filter.mp hB).1

  have hP2Short : ∀ B ∈ P2, ShortZero S B := by
    intro B hB
    exact hPShort B (Finset.mem_filter.mp hB).1

  have hP2Card : ∀ B ∈ P2, B.card = 2 := by
    intro B hB
    have hNotThree : B.card ≠ 3 := (Finset.mem_filter.mp hB).2
    rcases shortZero_card_two_or_three (hP2Short B hB) with hTwo | hThree
    · exact hTwo
    · exact (hNotThree hThree).elim

  have hPairSet : (P : Set (Finset (Fin 24))).PairwiseDisjoint id := by
    simpa [P] using s039AllBlocks_pairwiseDisjoint hAvoid

  have hSum3 : (∑ B ∈ P3, B.card) = 3 * l := by
    calc
      (∑ B ∈ P3, B.card) = ∑ _B ∈ P3, 3 := by
        apply Finset.sum_congr rfl
        intro B hB
        exact (Finset.mem_filter.mp hB).2
      _ = 3 * l := by simp [l, Nat.mul_comm]

  have hSum2 : (∑ B ∈ P2, B.card) = 2 * t := by
    calc
      (∑ B ∈ P2, B.card) = ∑ _B ∈ P2, 2 := by
        apply Finset.sum_congr rfl
        intro B hB
        exact hP2Card B hB
      _ = 2 * t := by simp [t, Nat.mul_comm]

  have hUnionCard : U.card = 3 * l + 2 * t := by
    have hSplit :=
      Finset.sum_filter_add_sum_filter_not P
        (fun B : Finset (Fin 24) => B.card = 3) (fun B => B.card)
    calc
      U.card = ∑ B ∈ P, B.card := by
        simpa [U] using Finset.card_biUnion hPairSet
      _ = (∑ B ∈ P3, B.card) + ∑ B ∈ P2, B.card := by
        simpa [P3, P2] using hSplit.symm
      _ = 3 * l + 2 * t := by rw [hSum3, hSum2]

  have hRemainderCount : r + U.card = 24 := by
    have h :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
    simpa [r] using h

  have hLength : l + 2 * s + r = 24 := by
    dsimp [s]
    omega

  have hLS : l ≤ s := by
    dsimp [s]
    omega

  -- The three-block residual used for the source bound l ≥ 6.
  let b3 : Fin l → Finset (Fin 24) :=
    fun i => (P3.equivFin.symm i).1
  have hb3Mem : ∀ i, b3 i ∈ P3 := by
    intro i
    exact (P3.equivFin.symm i).2
  have hb3Short : ∀ i, ShortZero S (b3 i) := by
    intro i
    exact hP3Short (b3 i) (hb3Mem i)
  have hb3Card : ∀ i, (b3 i).card = 3 := by
    intro i
    exact (Finset.mem_filter.mp (hb3Mem i)).2
  have hb3Pair :
      ∀ i j, i ≠ j → Disjoint (b3 i) (b3 j) := by
    intro i j hij
    apply shortZero_disjoint_of_ne hAvoid (hb3Short i) (hb3Short j)
    intro hBlocksEq
    apply hij
    apply (P3.equivFin.symm).injective
    apply Subtype.ext
    exact hBlocksEq

  let rep3 : Fin l → Fin 24 :=
    fun i => Classical.choose (hb3Short i).1
  have hrep3 : ∀ i, rep3 i ∈ b3 i := by
    intro i
    exact Classical.choose_spec (hb3Short i).1
  have hrep3Card : (representativeSet rep3).card = l :=
    representativeSet_card_of_pairwise hb3Pair hrep3

  let A3 : Finset (Fin 24) := Finset.univ \ representativeSet rep3
  have hA3Card : A3.card = 24 - l := by
    dsimp [A3]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), hrep3Card]
    simp

  have hNoThreeA3 :
      ∀ J : Finset (Fin 24), J ⊆ A3 →
        J.card = 3 → posSum S J ≠ 0 := by
    intro J hJA hJCard hJZero
    have hJShort : ShortZero S J := by
      refine ⟨Finset.card_pos.mp (by omega), by omega, hJZero⟩
    have hJP3 : J ∈ P3 := by
      simp [P3, P, hJShort, hJCard]
    let i : Fin l := P3.equivFin ⟨J, hJP3⟩
    have hi : b3 i = J := by
      simp [b3, i]
    have hrepInJ : rep3 i ∈ J := by
      rw [← hi]
      exact hrep3 i
    have hrepInSet : rep3 i ∈ representativeSet rep3 := by
      simp [representativeSet]
    exact (Finset.mem_sdiff.mp (hJA hrepInJ)).2 hrepInSet

  have hA3Le : A3.card ≤ 18 :=
    card_le_eighteen_of_threeTerm19 h19 S hNoThreeA3
  have hL : 6 ≤ l := by
    rw [hA3Card] at hA3Le
    omega

  -- The all-block residual used for the source bound s ≥ 8.
  let bAll : Fin P.card → Finset (Fin 24) :=
    fun i => (P.equivFin.symm i).1
  have hbAllMem : ∀ i, bAll i ∈ P := by
    intro i
    exact (P.equivFin.symm i).2
  have hbAllShort : ∀ i, ShortZero S (bAll i) := by
    intro i
    exact hPShort (bAll i) (hbAllMem i)
  have hbAllPair :
      ∀ i j, i ≠ j → Disjoint (bAll i) (bAll j) := by
    intro i j hij
    apply shortZero_disjoint_of_ne hAvoid (hbAllShort i) (hbAllShort j)
    intro hBlocksEq
    apply hij
    apply (P.equivFin.symm).injective
    apply Subtype.ext
    exact hBlocksEq

  let repAll : Fin P.card → Fin 24 :=
    fun i => Classical.choose (hbAllShort i).1
  have hrepAll : ∀ i, repAll i ∈ bAll i := by
    intro i
    exact Classical.choose_spec (hbAllShort i).1
  have hrepAllCard : (representativeSet repAll).card = P.card :=
    representativeSet_card_of_pairwise hbAllPair hrepAll

  let AAll : Finset (Fin 24) := Finset.univ \ representativeSet repAll
  have hAAllCard : AAll.card = 24 - P.card := by
    dsimp [AAll]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), hrepAllCard]
    simp

  have hAAllFree : ShortFreeOn S AAll := by
    intro J hJA hJShort
    have hJP : J ∈ P := by
      simpa [P] using hJShort
    let i : Fin P.card := P.equivFin ⟨J, hJP⟩
    have hi : bAll i = J := by
      simp [bAll, i]
    have hrepInJ : repAll i ∈ J := by
      rw [← hi]
      exact hrepAll i
    have hrepInSet : repAll i ∈ representativeSet repAll := by
      simp [representativeSet]
    exact (Finset.mem_sdiff.mp (hJA hrepInJ)).2 hrepInSet

  have hAAllLe : AAll.card ≤ 16 :=
    card_le_sixteen_of_eta17 hEta S hAAllFree
  have hS : 8 ≤ s := by
    rw [hAAllCard] at hAAllLe
    rw [hPCard] at hAAllLe
    omega

  have hSignature : S039Signature l s r :=
    s039_signature_of_arithmetic hL hS hLS hLength

  -- Enumerate three-blocks first and two-blocks second for the exact S039
  -- certificate interface.
  let b2 : Fin t → Finset (Fin 24) :=
    fun i => (P2.equivFin.symm i).1
  have hb2Mem : ∀ i, b2 i ∈ P2 := by
    intro i
    exact (P2.equivFin.symm i).2
  have hb2Short : ∀ i, ShortZero S (b2 i) := by
    intro i
    exact hP2Short (b2 i) (hb2Mem i)
  have hb2Card : ∀ i, (b2 i).card = 2 := by
    intro i
    exact hP2Card (b2 i) (hb2Mem i)

  let blocks : Fin s → Finset (Fin 24) := by
    dsimp [s]
    exact Fin.addCases b3 b2

  have hBlocksShort : ∀ j, ShortZero S (blocks j) := by
    intro j
    dsimp [s] at j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [blocks] using hb3Short i
    · simpa [blocks] using hb2Short i

  have hBlocksCard :
      ∀ j, (blocks j).card = (if j.val < l then 3 else 2) := by
    intro j
    dsimp [s] at j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have hi : (Fin.castAdd t i).val < l := i.isLt
      simp [blocks, hb3Card i, hi]
    · have hi : ¬(Fin.natAdd l i).val < l := by simp
      simp [blocks, hb2Card i, hi]

  have hBlocksInj : Function.Injective blocks := by
    intro i j hij
    dsimp [s] at i j
    obtain ⟨i' | i', rfl⟩ := finSumFinEquiv.surjective i
    · obtain ⟨j' | j', rfl⟩ := finSumFinEquiv.surjective j
      · have hEq : b3 i' = b3 j' := by
          simpa [blocks] using hij
        have hij' : i' = j' := by
          apply (P3.equivFin.symm).injective
          apply Subtype.ext
          exact hEq
        subst j'
        rfl
      · have hCardEq := congrArg Finset.card hij
        have hi3 := hb3Card i'
        have hj2 := hb2Card j'
        simp [blocks, hi3, hj2] at hCardEq
    · obtain ⟨j' | j', rfl⟩ := finSumFinEquiv.surjective j
      · have hCardEq := congrArg Finset.card hij
        have hi2 := hb2Card i'
        have hj3 := hb3Card j'
        simp [blocks, hi2, hj3] at hCardEq
      · have hEq : b2 i' = b2 j' := by
          simpa [blocks] using hij
        have hij' : i' = j' := by
          apply (P2.equivFin.symm).injective
          apply Subtype.ext
          exact hEq
        subst j'
        rfl

  have hBlocksMem : ∀ j, blocks j ∈ P := by
    intro j
    dsimp [s] at j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have h := (Finset.mem_filter.mp (hb3Mem i)).1
      simpa [blocks] using h
    · have h := (Finset.mem_filter.mp (hb2Mem i)).1
      simpa [blocks] using h

  have hBlocksPair :
      ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j) := by
    intro i j hij
    apply shortZero_disjoint_of_ne hAvoid (hBlocksShort i) (hBlocksShort j)
    intro hEq
    exact hij (hBlocksInj hEq)

  have hBlocksSurj :
      ∀ B ∈ P, ∃ j : Fin s, blocks j = B := by
    intro B hBP
    by_cases hThree : B.card = 3
    · have hBP3 : B ∈ P3 := by
        simp [P3, hBP, hThree]
      let i : Fin l := P3.equivFin ⟨B, hBP3⟩
      refine ⟨Fin.castAdd t i, ?_⟩
      simp [blocks, s, b3, i]
    · have hBP2 : B ∈ P2 := by
        simp [P2, hBP, hThree]
      let i : Fin t := P2.equivFin ⟨B, hBP2⟩
      refine ⟨Fin.natAdd l i, ?_⟩
      simp [blocks, s, b2, i]

  have hBlockUnion : blockUnion blocks = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Finset.mem_biUnion.mp hx
      have hBP : blocks j ∈ P := hBlocksMem j
      exact Finset.mem_biUnion.mpr ⟨blocks j, hBP, hj.2⟩
    · intro hx
      obtain ⟨B, hB⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨j, hj⟩ := hBlocksSurj B hB.1
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ j, ?_⟩
      simpa [hj] using hB.2

  have hCertificateResidual :
      ∀ rep : Fin s → Fin 24,
        (∀ j, rep j ∈ blocks j) →
        ShortFreeOn S (Finset.univ \ representativeSet rep) := by
    intro rep hrep
    intro J hJSub hJShort
    have hJP : J ∈ P := by
      simpa [P] using hJShort
    obtain ⟨j, hj⟩ := hBlocksSurj J hJP
    have hrepInJ : rep j ∈ J := by
      rw [← hj]
      exact hrep j
    have hrepInSet : rep j ∈ representativeSet rep := by
      simp [representativeSet]
    exact (Finset.mem_sdiff.mp (hJSub hrepInJ)).2 hrepInSet

  refine ⟨{
    s := s
    l := l
    r := r
    signature := hSignature
    blocks := blocks
    block_shortZero := hBlocksShort
    pairwise_disjoint := hBlocksPair
    block_card := hBlocksCard
    remainder_card := ?_
    every_representative_residual_shortFree := hCertificateResidual
  }⟩
  simpa [r, hBlockUnion]
end InverseZeroSum.Candidate3
