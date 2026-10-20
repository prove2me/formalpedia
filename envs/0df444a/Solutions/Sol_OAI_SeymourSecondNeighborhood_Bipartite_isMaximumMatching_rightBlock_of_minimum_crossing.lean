-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Bipartite.isMaximumMatching_rightBlock_of_minimum_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:00:50.14246+00:00
-- url     : https://prove2.me/submissions/2fb3cb2c-e7c2-4718-9b6c-762ae9589067

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatchingAugmented.lean:L18-L160
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Bipartite.isMaximumMatching_rightBlock_of_minimum_crossing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_matching_saturating_left_of_card_lt

-- ---- from OAI.Combinatorics.SecondNeighborhood.MatchingExchange ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} {E : L → R → Prop}

private theorem exchange_matching_subset {M N : Finset (L × R)}
    (hM : IsMatching E M) (hNM : N ⊆ M) : IsMatching E N := by
  exact ⟨fun e he => hM.1 e (hNM he),
    fun _ he _ hf h => hM.2.1 (hNM he) (hNM hf) h,
    fun _ he _ hf h => hM.2.2 (hNM he) (hNM hf) h⟩

theorem exists_matching_one_larger_saturating_left [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {M N : Finset (L × R)} (hM : IsMatching E M) (hN : IsMatching E N)
    (hcard : M.card < N.card) :
    ∃ Q : Finset (L × R), IsMatching E Q ∧ Q.card = M.card + 1 ∧
      M.image Prod.fst ⊆ Q.image Prod.fst := by
  classical
  obtain ⟨N', hN'N, hN'card⟩ :=
    Finset.exists_subset_card_eq (show M.card + 1 ≤ N.card by omega)
  obtain ⟨Q, hQ, hQcard, hQM⟩ :=
    exists_matching_saturating_left_of_card_lt hM
      (exchange_matching_subset hN hN'N) (by omega)
  exact ⟨Q, hQ, hQcard.trans hN'card, hQM⟩

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.MatchingAugmented ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {E : L → R → Prop}

omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in
private theorem augmented_matching_subset {M N : Finset (L × R)}
    (hM : IsMatching E M) (hNM : N ⊆ M) : IsMatching E N := by
  exact ⟨fun e he => hM.1 e (hNM he),
    fun _ he _ hf h => hM.2.1 (hNM he) (hNM hf) h,
    fun _ he _ hf h => hM.2.2 (hNM he) (hNM hf) h⟩

theorem isMaximumMatching_rightBlock_of_minimum_crossing
    (P : L → Prop) (Q : R → Prop) [DecidablePred P] [DecidablePred Q]
    (hblock : ∀ a b, E a b → Q b → P a)
    {M : Finset (L × R)} (hM : IsMaximumMatching E M)
    (hmin : ∀ N : Finset (L × R), IsMaximumMatching E N →
      (M.filter (fun e => P e.1 ∧ ¬Q e.2)).card ≤
        (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card) :
    IsMaximumMatching (fun a b => E a b ∧ Q b)
      (M.filter (fun e => Q e.2)) := by
  classical
  let α := M.filter (fun e => Q e.2)
  let T := M \ α
  have hαM : α ⊆ M := Finset.filter_subset _ _
  have hα : IsMatching (fun a b => E a b ∧ Q b) α := by
    refine ⟨?_, (augmented_matching_subset hM.1 hαM).2⟩
    intro e he
    exact ⟨hM.1.1 e (hαM he), (Finset.mem_filter.mp he).2⟩
  refine ⟨hα, ?_⟩
  intro N hN
  by_contra hlarge
  have hlarge' : α.card < N.card := Nat.lt_of_not_ge hlarge
  obtain ⟨B, hB, hBcard, hBleft⟩ :=
    exists_matching_one_larger_saturating_left hα hN hlarge'
  have hBE : IsMatching E B :=
    ⟨fun e he => (hB.1 e he).1, hB.2⟩
  have hT : IsMatching E T :=
    augmented_matching_subset hM.1 Finset.sdiff_subset
  have hTnotQ : ∀ e ∈ T, ¬Q e.2 := by
    intro e he hQ
    exact (Finset.mem_sdiff.mp he).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, hQ⟩)
  let D := T.filter (fun e => e.1 ∈ B.image Prod.fst)
  let U := T \ D
  let M' := U ∪ B
  have hDT : D ⊆ T := Finset.filter_subset _ _
  have hUM : U ⊆ M := fun e he =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
  have hDcross : ∀ e ∈ D, P e.1 ∧ ¬Q e.2 := by
    intro e he
    have heT := hDT he
    obtain ⟨b, hbB, hb⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).2
    refine ⟨?_, hTnotQ e heT⟩
    have hbP := hblock b.1 b.2 (hB.1 b hbB).1 (hB.1 b hbB).2
    simpa only [hb] using hbP
  have hDleft : D.image Prod.fst ⊆ B.image Prod.fst \ α.image Prod.fst := by
    intro a ha
    obtain ⟨e, heD, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp heD).2, ?_⟩
    intro heα
    obtain ⟨f, hfα, hfe⟩ := Finset.mem_image.mp heα
    have heM : e ∈ M := (Finset.mem_sdiff.mp (hDT heD)).1
    have hfe' : f = e := hM.1.2.1 (hαM hfα) heM hfe
    exact (Finset.mem_sdiff.mp (hDT heD)).2 (hfe' ▸ hfα)
  have hDcard : D.card ≤ 1 := by
    have hDinj : Set.InjOn Prod.fst (↑D : Set (L × R)) :=
      fun _ he _ hf h => hT.2.1 (hDT he) (hDT hf) h
    have hc := Finset.card_le_card hDleft
    rw [Finset.card_image_of_injOn hDinj,
      Finset.card_sdiff_of_subset hBleft,
      Finset.card_image_of_injOn hB.2.1,
      Finset.card_image_of_injOn hα.2.1] at hc
    omega
  have hUBleft : ∀ u ∈ U, ∀ b ∈ B, u.1 ≠ b.1 := by
    intro u hu b hb hub
    have huT : u ∈ T := (Finset.mem_sdiff.mp hu).1
    have huD : u ∈ D := Finset.mem_filter.mpr
      ⟨huT, Finset.mem_image.mpr ⟨b, hb, hub.symm⟩⟩
    exact (Finset.mem_sdiff.mp hu).2 huD
  have hUBright : ∀ u ∈ U, ∀ b ∈ B, u.2 ≠ b.2 := by
    intro u hu b hb hub
    apply hTnotQ u (Finset.mem_sdiff.mp hu).1
    rw [hub]
    exact (hB.1 b hb).2
  have hU : IsMatching E U := augmented_matching_subset hM.1 hUM
  have hM'match : IsMatching E M' := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hU.1 e he
      · exact hBE.1 e he
    · intro e he f hf hef
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp hf with hf | hf
        · exact hU.2.1 he hf hef
        · exact False.elim (hUBleft e he f hf hef)
      · rcases Finset.mem_union.mp hf with hf | hf
        · exact False.elim (hUBleft f hf e he hef.symm)
        · exact hBE.2.1 he hf hef
    · intro e he f hf hef
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp hf with hf | hf
        · exact hU.2.2 he hf hef
        · exact False.elim (hUBright e he f hf hef)
      · rcases Finset.mem_union.mp hf with hf | hf
        · exact False.elim (hUBright f hf e he hef.symm)
        · exact hBE.2.2 he hf hef
  have hUBdisjoint : Disjoint U B := by
    apply Finset.disjoint_left.mpr
    intro e heU heB
    exact hUBleft e heU e heB rfl
  have hM'card : M'.card + D.card = M.card + 1 := by
    have hpart := Finset.card_sdiff_add_card_eq_card hαM
    have hpart' := Finset.card_sdiff_add_card_eq_card hDT
    have hunion := Finset.card_union_of_disjoint hUBdisjoint
    change M'.card = U.card + B.card at hunion
    change T.card + α.card = M.card at hpart
    change U.card + D.card = T.card at hpart'
    omega
  have hM'le : M'.card ≤ M.card := hM.2 M' hM'match
  have hDeq : D.card = 1 := by omega
  have hM'eq : M'.card = M.card := by omega
  have hM'max : IsMaximumMatching E M' := by
    refine ⟨hM'match, ?_⟩
    intro N' hN'
    rw [hM'eq]
    exact hM.2 N' hN'
  let C := M.filter (fun e => P e.1 ∧ ¬Q e.2)
  have hDC : D ⊆ C := by
    intro e he
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp (hDT he)).1, hDcross e he⟩
  have hcost : M'.filter (fun e => P e.1 ∧ ¬Q e.2) = C \ D := by
    ext e
    constructor
    · intro he
      obtain ⟨he, hPe, hnQe⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_union.mp he with heU | heB
      · exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨hUM heU, hPe, hnQe⟩,
            (Finset.mem_sdiff.mp heU).2⟩
      · exact False.elim (hnQe (hB.1 e heB).2)
    · intro he
      obtain ⟨heC, heD⟩ := Finset.mem_sdiff.mp he
      obtain ⟨heM, hPe, hnQe⟩ := Finset.mem_filter.mp heC
      have heT : e ∈ T := Finset.mem_sdiff.mpr
        ⟨heM, fun heα => hnQe (Finset.mem_filter.mp heα).2⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨heT, heD⟩)), hPe, hnQe⟩
  have hmin' := hmin M' hM'max
  rw [hcost] at hmin'
  have hpart := Finset.card_sdiff_add_card_eq_card hDC
  change C.card ≤ (C \ D).card at hmin'
  omega

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Bipartite.isMaximumMatching_rightBlock_of_minimum_crossing := @_root_.OAI.SeymourSecondNeighborhood.Bipartite.isMaximumMatching_rightBlock_of_minimum_crossing
