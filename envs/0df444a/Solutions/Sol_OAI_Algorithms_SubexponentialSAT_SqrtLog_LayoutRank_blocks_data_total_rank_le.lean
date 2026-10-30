-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.blocks_data_total_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:04:52.681399+00:00
-- url     : https://prove2.me/submissions/6d756597-1420-472c-97e0-c1239f58a55a

import Mathlib
import Definitions.Def_OAIQ081S036
import Definitions.Def_OAIQ081S071

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BlockPacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Packing complete type blocks

The squared-deviation bound and the threshold from Section 5.4 imply a lower
bound for every type count. Enumerating the finite fibers then constructs
pairwise disjoint complete blocks. The construction from supplied enumerations
is explicit; no running-time theorem is asserted here.
-/

namespace SubexponentialSAT.BlockPacking

open scoped BigOperators

namespace CompleteBlocks

variable {α τ : Type*} {label : α → τ} {b : ℕ}

variable [Fintype τ]

variable [Fintype α] [DecidableEq α]

theorem card_leftovers_add_covered (P : CompleteBlocks label b) :
    P.leftovers.card + P.covered.card = Fintype.card α := by
  simpa only [leftovers, Finset.card_univ] using
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P.covered)

end CompleteBlocks

end SubexponentialSAT.BlockPacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rational row-space bounds for literal integer constraint families. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open Module LayoutPullback LayoutExactBuckets LayoutRowSelection

variable {J I V : Type*} [Fintype J] [Fintype I] [Fintype V]

omit [Fintype V] in
theorem rowRank_le_card (C : J → V → ℤ) : rowRank C ≤ Fintype.card J :=
  finrank_range_le_card (rationalRows C)

variable [DecidableEq V]

omit [Fintype J] in
omit [Fintype V] in
theorem rowSpace_pullback (owner : I → V) (C : J → I → ℤ) :
    rowSpace (pulledConstraints owner C) = (rowSpace C).map (rowLinear owner) := by
  rw [rowSpace, rowSpace, LinearMap.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℚ)
  apply congrArg Set.range
  funext j v
  exact row_map (Int.castRingHom ℚ) owner (C j) v

omit [Fintype J] in
omit [Fintype V] in
/-- Literal incidence pullback never increases rational constraint rank. -/
theorem rowRank_pullback_le (owner : I → V) (C : J → I → ℤ) :
    rowRank (pulledConstraints owner C) ≤ rowRank C := by
  unfold rowRank
  rw [rowSpace_pullback]
  exact Submodule.finrank_map_le _ _

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowSpace_reindex {K : Type*} [Fintype K] (C : J → V → ℤ)
    (e : K → J) (he : Function.Surjective e) :
    rowSpace (fun k => C (e k)) = rowSpace C := by
  unfold rowSpace
  congr 1
  exact he.range_comp (rationalRows C)

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowRank_reindex {K : Type*} [Fintype K] (C : J → V → ℤ)
    (e : K → J) (he : Function.Surjective e) :
    rowRank (fun k => C (e k)) = rowRank C := by
  unfold rowRank
  rw [rowSpace_reindex C e he]

omit [DecidableEq V] in
theorem finrank_biSup_le {K : Type*} (s : Finset K)
    (W : K → Submodule ℚ (V → ℚ)) :
    finrank ℚ (⨆ k ∈ s, W k : Submodule ℚ (V → ℚ)) ≤ ∑ k ∈ s, finrank ℚ (W k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hk]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

omit [DecidableEq V] in
theorem finrank_iSup_le {K : Type*} [Fintype K]
    (W : K → Submodule ℚ (V → ℚ)) :
    finrank ℚ (⨆ k, W k : Submodule ℚ (V → ℚ)) ≤ ∑ k, finrank ℚ (W k) := by
  have he : (⨆ k ∈ (Finset.univ : Finset K), W k) = ⨆ k, W k := by
    apply le_antisymm
    · exact iSup_le (fun k => iSup_le (fun _ => le_iSup W k))
    · exact iSup_le (fun k => le_iSup_of_le k
        (le_iSup_of_le (Finset.mem_univ k) le_rfl))
  have h := finrank_biSup_le (Finset.univ : Finset K) W
  rw [he] at h
  exact h

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowSpace_product {K : Type*} [Fintype K] (C : K → J → V → ℤ) :
    rowSpace (fun p : K × J => C p.1 p.2) = ⨆ k, rowSpace (C k) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨k,j⟩, rfl⟩
    exact (le_iSup (fun k => rowSpace (C k)) k)
      (Submodule.subset_span ⟨j, rfl⟩)
  · apply iSup_le
    intro k
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨(k,j), rfl⟩

omit [Fintype J] in
omit [DecidableEq V] in
theorem rowRank_product_le {K : Type*} [Fintype K] (C : K → J → V → ℤ) :
    rowRank (fun p : K × J => C p.1 p.2) ≤ ∑ k, rowRank (C k) := by
  unfold rowRank
  rw [rowSpace_product]
  exact finrank_iSup_le _

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowSpace_sum {K : Type*} [Fintype K] (C : J → V → ℤ) (D : K → V → ℤ) :
    rowSpace (Sum.elim C D) = rowSpace C ⊔ rowSpace D := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    cases j with
    | inl j =>
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)
    | inr k =>
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)
  · apply sup_le
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨Sum.inl j, rfl⟩
    · apply Submodule.span_mono
      rintro _ ⟨k, rfl⟩
      exact ⟨Sum.inr k, rfl⟩

omit [Fintype J] [DecidableEq V] in
theorem rowRank_sum_le {K : Type*} [Fintype K] (C : J → V → ℤ) (D : K → V → ℤ) :
    rowRank (Sum.elim C D) ≤ rowRank C + rowRank D := by
  unfold rowRank
  rw [rowSpace_sum]
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

omit [Fintype J] in
/-- Any number of embedded block row families, plus arbitrary leftover rows. -/
theorem blocks_and_leftovers_rank_le {K L : Type*} [Fintype K] [Fintype L]
    (owner : K → I → V) (C : J → I → ℤ) (D : L → V → ℤ) :
    rowRank (Sum.elim (fun p : K × J => row (owner p.1) (C p.2)) D) ≤
      Fintype.card K * rowRank C + Fintype.card L := by
  apply (rowRank_sum_le _ _).trans
  apply Nat.add_le_add _ (rowRank_le_card D)
  calc
    _ ≤ ∑ k, rowRank (pulledConstraints (owner k) C) := rowRank_product_le _
    _ ≤ ∑ _k : K, rowRank C := Finset.sum_le_sum (fun k _ => rowRank_pullback_le (owner k) C)
    _ = _ := by simp

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRankCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Disjoint head counts and the single total uncovered-coordinate budget. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes

variable {I U G : Type*} [Fintype I] [Fintype U] [Fintype G]
variable [DecidableEq I] [DecidableEq G]

omit [DecidableEq I] in
theorem sum_card_heads (head : I → G) :
    (∑ g, Fintype.card {i : I // head i = g}) = Fintype.card I := by
  simpa using Fintype.sum_fiberwise head (fun _ : I => (1 : ℕ))

omit [DecidableEq I] in
theorem sum_card_restricted_heads (head : I → G) (p : I → Prop) [DecidablePred p] :
    (∑ g, Fintype.card {v : {i : I // head i = g} // p v.val}) =
      Fintype.card {i : I // p i} := by
  have he (g : G) :
      Fintype.card {v : {i : I // head i = g} // p v.val} =
        Fintype.card {v : {i : I // p i} // head v.val = g} := by
    apply Fintype.card_congr
    exact {
      toFun := fun v => ⟨⟨v.val.val, v.property⟩, v.val.property⟩
      invFun := fun v => ⟨⟨v.val.val, v.property⟩, v.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp_rw [he]
  exact sum_card_heads (fun v : {i : I // p i} => head v.val)

variable {b : ℕ} {label : I → U}

theorem card_uncovered_eq (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) :
    Fintype.card {i : I // i ∉ Set.range P.embed} = P.leftovers.card := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp [SubexponentialSAT.BlockPacking.CompleteBlocks.leftovers,
    SubexponentialSAT.BlockPacking.CompleteBlocks.covered, Set.mem_range]

theorem sum_card_uncovered_heads (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (head : I → G) :
    (∑ g, Fintype.card {v : {i : I // head i = g} // v.val ∉ Set.range P.embed}) =
      P.leftovers.card := by
  classical
  exact (sum_card_restricted_heads head (fun i => i ∉ Set.range P.embed)).trans
    (card_uncovered_eq P)

/-- Coverage pays for leftover coordinates once in the total rank sum. -/
theorem block_budget_le (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (ε : ℚ) (hε : 0 ≤ ε)
    (hcover : (1 - ε) * (Fintype.card I : ℚ) ≤ b * (Fintype.card U : ℚ)) :
    (b : ℚ) * (ε * Fintype.card U) + P.leftovers.card ≤
      2 * ε * Fintype.card I := by
  have hsum : (P.leftovers.card : ℚ) + (b : ℚ) * Fintype.card U = Fintype.card I := by
    have h : P.leftovers.card + b * Fintype.card U = Fintype.card I := by
      simpa using P.card_leftovers_add_covered
    exact_mod_cast h
  have hpacked : (b : ℚ) * Fintype.card U ≤ Fintype.card I := by
    have hnonneg : (0 : ℚ) ≤ P.leftovers.card := by positivity
    linarith
  have hfirst : (b : ℚ) * (ε * Fintype.card U) ≤ ε * Fintype.card I := by
    nlinarith [mul_le_mul_of_nonneg_left hpacked hε]
  have hleft : (P.leftovers.card : ℚ) ≤ ε * Fintype.card I := by linarith
  linarith

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRankBlocks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rank accumulation for the concrete complete-block layout and its pullback. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes LayoutPullback LayoutExactBuckets

variable {U I V F G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R b : ℕ} {label : I → U}

omit [Fintype G] in
theorem block_constraints_rank_le
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) :
    rowRank (LayoutBlocks.constraints C P t g) ≤ b * rowRank (C.constraints t g) +
      Fintype.card {v : {i : I // LayoutBlocks.copyHead C label t i = g} //
        v.val ∉ Set.range P.embed} := by
  have he : LayoutBlocks.constraints C P t g =
      Sum.elim (fun p => row (LayoutBlocks.embedHead C P t g p.1) (C.constraints t g p.2))
        (fun v => Pi.single v.val (1 : ℤ)) := by
    funext j
    cases j <;> rfl
  rw [he]
  simpa only [Fintype.card_fin] using blocks_and_leftovers_rank_le (LayoutBlocks.embedHead C P t g)
    (C.constraints t g)
    (fun v : {v : {i : I // LayoutBlocks.copyHead C label t i = g} //
      v.val ∉ Set.range P.embed} => Pi.single v.val (1 : ℤ))

theorem blocks_total_rank_le
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) :
    (∑ g, (rowRank (LayoutBlocks.constraints C P t g) : ℚ)) ≤
      (b : ℚ) * ∑ g, (rowRank (C.constraints t g) : ℚ) + P.leftovers.card := by
  calc
    _ ≤ ∑ g, ((b : ℚ) * rowRank (C.constraints t g) +
        Fintype.card {v : {i : I // LayoutBlocks.copyHead C label t i = g} //
          v.val ∉ Set.range P.embed}) := by
      apply Finset.sum_le_sum
      intro g _
      exact_mod_cast block_constraints_rank_le C P t g
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      exact_mod_cast sum_card_uncovered_heads P (LayoutBlocks.copyHead C label t)

omit [Fintype G] in
theorem blocks_data_rank_eq
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t)
    (t : Fin Q) (g : G) :
    rowRank ((LayoutBlocks.data C P factor color hcolor).constraints t g) =
      rowRank (LayoutBlocks.constraints C P t g) := by
  change rowRank (fun j => LayoutBlocks.constraints C P t g
    ((Fintype.equivFin (LayoutBlocks.RowIndex C P t g)).symm j)) = _
  exact rowRank_reindex _ _ (Equiv.surjective _)

theorem blocks_data_total_rank_le_oai
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t)
    (t : Fin Q) (ε : ℚ) (hε : 0 ≤ ε)
    (hbase : (∑ g, (rowRank (C.constraints t g) : ℚ)) ≤ ε * Fintype.card U)
    (hcover : (1 - ε) * (Fintype.card I : ℚ) ≤ b * (Fintype.card U : ℚ)) :
    (∑ g, (rowRank ((LayoutBlocks.data C P factor color hcolor).constraints t g) : ℚ)) ≤
      2 * ε * Fintype.card I := by
  simp_rw [blocks_data_rank_eq]
  calc
    _ ≤ (b : ℚ) * ∑ g, (rowRank (C.constraints t g) : ℚ) + P.leftovers.card :=
      blocks_total_rank_le C P t
    _ ≤ (b : ℚ) * (ε * Fintype.card U) + P.leftovers.card := by gcongr
    _ ≤ _ := block_budget_le P ε hε hcover

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

theorem solution.{u_1, u_2, u_4, u_5, u_6} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.blocks_data_total_rank_le_oai.{u_1, u_2, u_4, u_5, u_6} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.blocks_data_total_rank_le_oai.{u_1, u_2, u_4, u_5, u_6}
