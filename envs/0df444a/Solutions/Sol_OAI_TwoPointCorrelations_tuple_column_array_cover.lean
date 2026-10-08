-- Prove2me | solution 1 for OAI.TwoPointCorrelations.tuple_column_array_cover
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:44:16.718475+00:00
-- url     : https://prove2.me/submissions/3143403d-6452-4e77-8523-6306c062abec

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}





lemma forestRoots_subset (t : BinaryTree V) : forestRoots t ⊆ forestNodes t := by
  induction t with
  | nil => simp [forestRoots, forestNodes]
  | node v l r hl hr =>
      intro x hx
      simp only [forestRoots, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp [forestNodes]
      · simp [forestNodes, hr hx]


lemma forestAdjacent_mem (t : BinaryTree V) {x y : V} (h : forestAdjacent t x y) :
    x ∈ forestNodes t ∧ y ∈ forestNodes t := by
  induction t with
  | nil => exact h.elim
  | node v l r hl hr =>
      rcases h with ⟨rfl, hy⟩ | ⟨rfl, hx⟩ | h | h
      · simp [forestNodes, forestRoots_subset l hy]
      · simp [forestNodes, forestRoots_subset l hx]
      · obtain ⟨hx, hy⟩ := hl h
        simp [forestNodes, hx, hy]
      · obtain ⟨hx, hy⟩ := hr h
        simp [forestNodes, hx, hy]



lemma attachForestLeaf_of_not_mem [DecidableEq V] (parent leaf : V) (t : BinaryTree V)
    (hp : parent ∉ forestNodes t) : attachForestLeaf parent leaf t = t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      have hv : v ≠ parent := by intro h; subst v; exact hp (by simp [forestNodes])
      have hpl : parent ∉ forestNodes l := by intro h; exact hp (by simp [forestNodes, h])
      have hpr : parent ∉ forestNodes r := by intro h; exact hp (by simp [forestNodes, h])
      simp only [attachForestLeaf, if_neg hv, hl hpl, hr hpr]

@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]

lemma attachForestLeaf_nodes_perm [DecidableEq V] (parent leaf : V) (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hp : parent ∈ forestNodes t) :
    (forestNodes (attachForestLeaf parent leaf t)).Perm (leaf :: forestNodes t) := by
  induction t with
  | nil => simp [forestNodes] at hp
  | node v l r hl hr =>
      have hnodup := List.nodup_cons.mp ht
      have hparts := List.nodup_append.mp hnodup.2
      by_cases hv : v = parent
      · simp only [attachForestLeaf, if_pos hv, forestNodes, List.nil_append]
        exact List.Perm.swap _ _ _
      · have hp' : parent ∈ forestNodes l ∨ parent ∈ forestNodes r := by
          simpa only [forestNodes, List.mem_cons, List.mem_append, Ne.symm hv, false_or] using hp
        rcases hp' with hp' | hp'
        · have hpr : parent ∉ forestNodes r := by
            intro hpr
            exact hparts.2.2 parent hp' parent hpr rfl
          rw [attachForestLeaf, if_neg hv, attachForestLeaf_of_not_mem parent leaf r hpr]
          simp only [forestNodes]
          exact ((hl hparts.1 hp').append_right _).cons v |>.trans (List.Perm.swap _ _ _)
        · have hpl : parent ∉ forestNodes l := by
            intro hpl
            exact hparts.2.2 parent hpl parent hp' rfl
          rw [attachForestLeaf, if_neg hv, attachForestLeaf_of_not_mem parent leaf l hpl]
          simp only [forestNodes]
          have hperm := ((hr hparts.2.1 hp').append_left (forestNodes l)).cons v
          exact hperm.trans ((List.perm_middle.cons v).trans (List.Perm.swap _ _ _))



private lemma move_two_disjuncts (A B C D E F : Prop) :
    (A ∨ B ∨ (C ∨ E ∨ F) ∨ D) ↔ (A ∨ B ∨ C ∨ D) ∨ E ∨ F := by
  tauto

lemma attachForestLeaf_adjacent [DecidableEq V] (parent leaf : V) (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hp : parent ∈ forestNodes t) (x y : V) :
    forestAdjacent (attachForestLeaf parent leaf t) x y ↔
      forestAdjacent t x y ∨ (x = parent ∧ y = leaf) ∨ (y = parent ∧ x = leaf) := by
  induction t with
  | nil => simp [forestNodes] at hp
  | node v l r hl hr =>
      have hnodup := List.nodup_cons.mp ht
      have hparts := List.nodup_append.mp hnodup.2
      by_cases hv : v = parent
      · subst v
        rw [attachForestLeaf, if_pos rfl]
        simp only [forestAdjacent, forestRoots, List.mem_cons,
          List.not_mem_nil, and_false, false_or, and_or_left]
        constructor
        · rintro ((h | h) | (h | h) | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
        · rintro ((h | h | h | h) | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inl (Or.inr h))
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl (Or.inl h))
      · have hp' : parent ∈ forestNodes l ∨ parent ∈ forestNodes r := by
          simpa only [forestNodes, List.mem_cons, List.mem_append, Ne.symm hv, false_or] using hp
        rcases hp' with hp' | hp'
        · have hpr : parent ∉ forestNodes r := by
            intro hpr
            exact hparts.2.2 parent hp' parent hpr rfl
          rw [attachForestLeaf, if_neg hv, attachForestLeaf_of_not_mem parent leaf r hpr]
          simp only [forestAdjacent, attachForestLeaf_roots, hl hparts.1 hp']
          exact move_two_disjuncts _ _ _ _ _ _
        · have hpl : parent ∉ forestNodes l := by
            intro hpl
            exact hparts.2.2 parent hpl parent hp' rfl
          rw [attachForestLeaf, if_neg hv, attachForestLeaf_of_not_mem parent leaf l hpl]
          simp only [forestAdjacent, hr hparts.2.1 hp', or_assoc]

lemma attachForestLeaf_nodup [DecidableEq V] (parent leaf : V) (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hp : parent ∈ forestNodes t) (hf : leaf ∉ forestNodes t) :
    (forestNodes (attachForestLeaf parent leaf t)).Nodup := by
  exact (attachForestLeaf_nodes_perm parent leaf t ht hp).nodup_iff.mpr
    (List.nodup_cons.mpr ⟨hf, ht⟩)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]






end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw











end FiniteLaw



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode
namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}


@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuotientLines
namespace OAI

/-!
# Quotient coordinates in the forest code

The quotient keeps a basis chosen from the original coordinate directions.
Failure to extend an independent family by a direction and a departure
difference forces that difference onto the corresponding quotient line.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule

variable {K ι κ V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The exact maximality consequence used for a regular label. -/
theorem quotient_line_of_nonextendable_pair (v : κ → V) (hv : LinearIndependent K v)
    (x y : V) (hx : (span K (Set.range v)).mkQ x ≠ 0)
    (hmax : ¬LinearIndependent K (Sum.elim v ![y, x])) :
    ∃ c : K, (span K (Set.range v)).mkQ y = c • (span K (Set.range v)).mkQ x := by
  classical
  let D := span K (Set.range v)
  let vlift : κ → D := fun i => ⟨v i, subset_span ⟨i, rfl⟩⟩
  have hvlift : LinearIndependent K vlift := by
    apply LinearIndependent.of_comp D.subtype
    exact hv
  have hq : ¬LinearIndependent K (D.mkQ ∘ ![y, x]) := by
    intro h
    apply hmax
    exact hvlift.sumElim_of_quotient ![y, x] h
  have heq : ∃ c : K, c • D.mkQ x = D.mkQ y := by
    by_contra! hc
    apply hq
    apply linearIndependent_fin2.mpr
    exact ⟨hx, hc⟩
  obtain ⟨c, hc⟩ := heq
  exact ⟨c, hc.symm⟩


/-- A coordinate basis survives the quotient after exactly `dim D` labels
are omitted. This fixes the count, even when the subspace is not spanned by
coordinate vectors. -/
theorem exists_coordinate_quotient_basis [Fintype ι] [DecidableEq ι]
    (D : Submodule K (ι → K)) :
    ∃ S : Finset ι, Sᶜ.card = Module.finrank K D ∧
      LinearIndependent K (fun i : S => D.mkQ (Pi.basisFun K ι i)) ∧
      span K (Set.range (fun i : S => D.mkQ (Pi.basisFun K ι i))) = ⊤ := by
  classical
  let v : ι → ((ι → K) ⧸ D) := fun i => D.mkQ (Pi.basisFun K ι i)
  have hv : span K (Set.range v) = ⊤ := by
    change span K (Set.range (D.mkQ ∘ Pi.basisFun K ι)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun K ι).span_eq,
      Submodule.map_top, LinearMap.range_eq_top.mpr D.mkQ_surjective]
  obtain ⟨η, a, ha, hspan, hind⟩ := exists_linearIndependent' K v
  let : Finite η := Finite.of_injective a ha
  let : Fintype η := Fintype.ofFinite η
  let b : Module.Basis η K ((ι → K) ⧸ D) := Module.Basis.mk hind (by rw [hspan, hv])
  let S : Finset ι := univ.image a
  let e : η ≃ S := Equiv.ofBijective (fun j => ⟨a j, mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩)
    ⟨fun j k h => ha (congrArg Subtype.val h), by
      intro i
      obtain ⟨j, _, hj⟩ := mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩⟩
  let bs := b.reindex e
  have hbs (i : S) : bs i = v i := by
    rw [show bs = b.reindex e from rfl, Module.Basis.reindex_apply]
    simp only [b, Module.Basis.mk_apply, Function.comp_apply]
    have hi : a (e.symm i) = i := congrArg Subtype.val (e.apply_symm_apply i)
    rw [hi]
  have heq : (bs : S → ((ι → K) ⧸ D)) = (fun i : S => D.mkQ (Pi.basisFun K ι i)) :=
    funext hbs
  have hcard : S.card = Module.finrank K ((ι → K) ⧸ D) := by
    simpa only [Fintype.card_coe] using (Module.finrank_eq_card_basis bs).symm
  have hdim := D.finrank_quotient_add_finrank
  rw [Module.finrank_pi] at hdim
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [card_compl, hcard]
    omega
  · rw [← heq]
    exact bs.linearIndependent
  · rw [← heq]
    exact bs.span_eq

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MaximalPairs
namespace OAI

/-! Finite maximal selection of jointly independent direction/difference pairs. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule

variable {K κ V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype κ] [DecidableEq κ]



omit [Fintype κ] in
private theorem independent_insert_pair (v : κ → Fin 2 → V) (S : Finset κ)
    (k : κ) (hk : k ∉ S)
    (h : LinearIndependent K (Sum.elim (pairFamily v S) (v k))) :
    LinearIndependent K (pairFamily v (insert k S)) := by
  apply (linearIndependent_equiv (insertPairEquiv S k hk)).mp
  convert (preTransparency := .instances) h using 1
  funext z
  cases z <;> rfl

/-- A maximal collection exists among the finitely many candidate pairs.
No further pair can be adjoined, and its span has twice the selected size. -/
theorem exists_maximal_independent_pairs (v : κ → Fin 2 → V) :
    ∃ S : Finset κ, LinearIndependent K (pairFamily v S) ∧
      Module.finrank K (span K (Set.range (pairFamily v S))) = 2 * S.card ∧
      ∀ k ∉ S, ¬LinearIndependent K (Sum.elim (pairFamily v S) (v k)) := by
  classical
  let good : Finset (Finset κ) := univ.filter (fun S => LinearIndependent K (pairFamily v S))
  have hempty : (∅ : Finset κ) ∈ good := by
    simp only [good, mem_filter, mem_univ, true_and]
    exact linearIndependent_empty_type
  obtain ⟨S, hS, hmax⟩ := good.exists_max_image Finset.card ⟨∅, hempty⟩
  have hind := (mem_filter.mp hS).2
  refine ⟨S, hind, ?_, ?_⟩
  · rw [finrank_span_eq_card hind, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    omega
  · intro k hk hnew
    have hgood : insert k S ∈ good := by
      exact mem_filter.mpr ⟨mem_univ _, independent_insert_pair v S k hk hnew⟩
    have hc := hmax (insert k S) hgood
    rw [card_insert_of_notMem hk] at hc
    omega



omit [Fintype κ] [DecidableEq κ] in
/-- Restriction to fewer candidate pairs preserves joint independence. -/
theorem independent_pairFamily_mono (v : κ → Fin 2 → V) {S T : Finset κ}
    (hTS : T ⊆ S) (hS : LinearIndependent K (pairFamily v S)) :
    LinearIndependent K (pairFamily v T) := by
  let f : T × Fin 2 → S × Fin 2 := fun z => (⟨z.1, hTS z.1.property⟩, z.2)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : S × Fin 2 => (z.1 : κ)) hxy
    · exact congrArg (fun z : S × Fin 2 => z.2) hxy
  exact hS.comp f hf

/-- Excluding `r` independent pairs bounds every maximal collection by `r-1`. -/
theorem exists_small_maximal_independent_pairs (v : κ → Fin 2 → V) (r : ℕ)
    (hno : ∀ S : Finset κ, S.card = r → ¬LinearIndependent K (pairFamily v S)) :
    ∃ S : Finset κ, S.card < r ∧ LinearIndependent K (pairFamily v S) ∧
      Module.finrank K (span K (Set.range (pairFamily v S))) = 2 * S.card ∧
      ∀ k ∉ S, ¬LinearIndependent K (Sum.elim (pairFamily v S) (v k)) := by
  obtain ⟨S, hS, hdim, hmax⟩ := exists_maximal_independent_pairs (K := K) v
  refine ⟨S, ?_, hS, hdim, hmax⟩
  by_contra h
  obtain ⟨T, hTS, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  exact hno T hcard (independent_pairFamily_mono v hTS hS)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RunPartition
namespace OAI

/-! Cutting a compressed perfect block into regular segments and omitted runs. -/

namespace TwoPointCorrelations

variable {α : Type*}


/-- Cutting does not reorder, omit or duplicate any compressed run. -/
theorem partitionColumnRuns_flatten (omitted : α → Bool) (runs : List α) :
    (partitionColumnRuns omitted runs).flatMap (Sum.elim id List.singleton) = runs := by
  induction runs with
  | nil => rfl
  | cons a rest ih =>
      cases ha : omitted a with
      | true => simpa [partitionColumnRuns, ha, List.singleton] using congrArg (List.cons a) ih
      | false =>
          cases ht : partitionColumnRuns omitted rest with
          | nil => simpa [partitionColumnRuns, ha, ht] using congrArg (List.cons a) ih
          | cons head tail =>
              cases head <;> simpa [partitionColumnRuns, ha, ht] using congrArg (List.cons a) ih

/-- The omitted part is exactly the original subsequence of omitted runs. -/
theorem partitionColumnRuns_omitted (omitted : α → Bool) (runs : List α) :
    (partitionColumnRuns omitted runs).filterMap (Sum.elim (fun _ => none) some) =
      runs.filter omitted := by
  induction runs with
  | nil => rfl
  | cons a rest ih =>
      cases ha : omitted a with
      | true => simpa [partitionColumnRuns, ha, List.filterMap_cons, Sum.elim] using
          congrArg (List.cons a) ih
      | false =>
          cases ht : partitionColumnRuns omitted rest with
          | nil => simpa [partitionColumnRuns, ha, ht, List.filterMap_cons, Sum.elim] using ih
          | cons head tail =>
              cases head <;> simpa [partitionColumnRuns, ha, ht, List.filterMap_cons, Sum.elim] using ih

/-- A merge mask needs no more slots than the compressed run list. -/
theorem partitionColumnRuns_length_le (omitted : α → Bool) (runs : List α) :
    (partitionColumnRuns omitted runs).length ≤ runs.length := by
  induction runs with
  | nil => simp [partitionColumnRuns]
  | cons a rest ih =>
      cases ha : omitted a with
      | true => simpa [partitionColumnRuns, ha] using Nat.succ_le_succ ih
      | false =>
          cases ht : partitionColumnRuns omitted rest with
          | nil => simp [partitionColumnRuns, ha, ht]
          | cons head tail =>
              cases head with
              | inl segment =>
                  simp only [ht, List.length_cons] at ih
                  simpa [partitionColumnRuns, ha, ht] using ih.trans (Nat.le_succ _)
              | inr label => simpa [partitionColumnRuns, ha, ht] using Nat.succ_le_succ ih




/-- Every regular segment except a possible initial one is charged to an
omitted run. The stronger head-sensitive form makes the induction exact. -/
theorem partitionColumnRuns_count_strong (omitted : α → Bool) (runs : List α) :
    regularPieceCount (partitionColumnRuns omitted runs) ≤
      omittedPieceCount (partitionColumnRuns omitted runs) +
        if startsWithRegularPiece (partitionColumnRuns omitted runs) then 1 else 0 := by
  induction runs with
  | nil => simp [partitionColumnRuns, regularPieceCount, omittedPieceCount, startsWithRegularPiece]
  | cons a rest ih =>
      cases ht : partitionColumnRuns omitted rest with
      | nil =>
          cases ha : omitted a <;>
            simp [partitionColumnRuns, ha, ht, regularPieceCount, omittedPieceCount,
              startsWithRegularPiece, List.filterMap_cons, Sum.elim]
      | cons head tail =>
          cases head <;> cases ha : omitted a <;>
            simp [partitionColumnRuns, ha, ht, regularPieceCount, omittedPieceCount,
              startsWithRegularPiece, List.filterMap_cons, Sum.elim] at ih ⊢ <;> omega

theorem partitionColumnRuns_regular_count (omitted : α → Bool) (runs : List α) :
    regularPieceCount (partitionColumnRuns omitted runs) ≤ (runs.filter omitted).length + 1 := by
  have h := partitionColumnRuns_count_strong omitted runs
  have ho : omittedPieceCount (partitionColumnRuns omitted runs) = (runs.filter omitted).length := by
    exact congrArg List.length (partitionColumnRuns_omitted omitted runs)
  rw [ho] at h
  split_ifs at h <;> omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RunPartitionProperties
namespace OAI

/-! The omitted-label cut retains the actual adjacency of every regular segment. -/

namespace TwoPointCorrelations

variable {α β : Type*}

/-- Every regular piece is a contiguous part of the original run list. -/
theorem partitionColumnRuns_regular_infix (omitted : α → Bool) (runs segment : List α)
    (hsegment : Sum.inl segment ∈ partitionColumnRuns omitted runs) :
    segment.IsInfix runs := by
  have hm : segment ∈ (partitionColumnRuns omitted runs).map (Sum.elim id List.singleton) :=
    List.mem_map.mpr ⟨.inl segment, hsegment, rfl⟩
  have hi := List.infix_of_mem_flatten hm
  change segment.IsInfix ((partitionColumnRuns omitted runs).flatMap (Sum.elim id List.singleton)) at hi
  rwa [partitionColumnRuns_flatten] at hi

/-- Cutting out omitted runs does not create new adjacent pairs inside a piece. -/
theorem partitionColumnRuns_regular_chain (R : α → α → Prop)
    (omitted : α → Bool) (runs segment : List α) (hchain : runs.IsChain R)
    (hsegment : Sum.inl segment ∈ partitionColumnRuns omitted runs) :
    segment.IsChain R :=
  hchain.infix (partitionColumnRuns_regular_infix omitted runs segment hsegment)

/-- The cut algorithm produces only nonempty regular pieces, all of whose
entries really are regular. -/
theorem partitionColumnRuns_regular_entries (omitted : α → Bool) (runs : List α) :
    ∀ segment, Sum.inl segment ∈ partitionColumnRuns omitted runs →
      segment ≠ [] ∧ ∀ a ∈ segment, omitted a = false := by
  induction runs with
  | nil => simp [partitionColumnRuns]
  | cons a rest ih =>
      intro segment hs
      cases ha : omitted a with
      | true =>
          simp only [partitionColumnRuns, ha, ↓reduceIte,
            List.mem_cons, Sum.inl_ne_inr, false_or] at hs
          exact ih segment hs
      | false =>
          cases ht : partitionColumnRuns omitted rest with
          | nil =>
              simp only [partitionColumnRuns, ha, Bool.false_eq_true, ↓reduceIte, ht,
                List.mem_singleton, Sum.inl.injEq] at hs
              subst segment
              simp [ha]
          | cons head tail =>
              cases head with
              | inl old =>
                  have hold := ih old (by rw [ht]; simp)
                  simp only [partitionColumnRuns, ha, Bool.false_eq_true, ↓reduceIte, ht,
                    List.mem_cons, Sum.inl.injEq] at hs
                  rcases hs with rfl | hs
                  · exact ⟨List.cons_ne_nil _ _, fun b hb => by
                      rcases List.mem_cons.mp hb with rfl | hb
                      · exact ha
                      · exact hold.2 b hb⟩
                  · exact ih segment (by rw [ht]; exact List.mem_cons_of_mem _ hs)
              | inr b =>
                  simp only [partitionColumnRuns, ha, Bool.false_eq_true, ↓reduceIte, ht,
                    List.mem_cons, Sum.inl.injEq, Sum.inl_ne_inr, false_or] at hs
                  rcases hs with rfl | hs
                  · simp [ha]
                  · exact ih segment (by rw [ht]; exact List.mem_cons_of_mem _ hs)

/-- Run positions and their labels may be cut in parallel: the algorithm
uses only the omitted predicate, so forgetting the positions commutes with it. -/
theorem partitionColumnRuns_map (f : α → β) (omitted : β → Bool) (runs : List α) :
    partitionColumnRuns omitted (runs.map f) =
      (partitionColumnRuns (fun a => omitted (f a)) runs).map (Sum.map (List.map f) f) := by
  induction runs with
  | nil => rfl
  | cons a rest ih =>
      cases ha : omitted (f a) with
      | true => simpa [partitionColumnRuns, ha] using congrArg (List.cons (.inr (f a))) ih
      | false =>
          cases ht : partitionColumnRuns (fun a => omitted (f a)) rest with
          | nil => simp [partitionColumnRuns, ha, ht, ih]
          | cons head tail =>
              cases head <;> simp [partitionColumnRuns, ha, ht, ih, Sum.map]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]


namespace FiniteLaw





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRepresentatives
namespace OAI

/-! Canonical occurrence representatives for the imperfect-position code. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α] {N : ℕ}




lemma columnRepresentative_mem (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    columnRepresentative label perfect i ∈ columnRepresentativeCandidates label perfect i :=
  min'_mem _ _

/-- A reference always carries the intended label. -/
theorem columnRepresentative_label (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    label (columnRepresentative label perfect i) = label i := by
  have hm := columnRepresentative_mem label perfect i
  dsimp only [columnRepresentativeCandidates] at hm
  split_ifs at hm <;> exact (mem_filter.mp hm).2

/-- Perfect occurrences are preferred whenever the class has one. -/
theorem columnRepresentative_perfect (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N)
    (h : ∃ j ∈ perfect, label j = label i) : columnRepresentative label perfect i ∈ perfect := by
  have hp : (perfect.filter (fun j => label j = label i)).Nonempty := by
    obtain ⟨j, hj, heq⟩ := h
    exact ⟨j, mem_filter.mpr ⟨hj, heq⟩⟩
  have hm := columnRepresentative_mem label perfect i
  simp only [columnRepresentativeCandidates, hp, ite_true] at hm
  exact (mem_filter.mp hm).1


theorem columnRepresentative_eq_iff (label : Fin N → α) (perfect : Finset (Fin N))
    (i j : Fin N) : columnRepresentative label perfect i = columnRepresentative label perfect j ↔
      label i = label j := by
  constructor
  · intro h
    exact (columnRepresentative_label label perfect i).symm.trans
      ((congrArg label h).trans (columnRepresentative_label label perfect j))
  · intro h
    have hc : columnRepresentativeCandidates label perfect i =
        columnRepresentativeCandidates label perfect j := by
      simp only [columnRepresentativeCandidates, h]
    unfold columnRepresentative
    simp only [hc]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestLeaves
namespace OAI

/-! Every finite nonempty forest has a vertex with at most one neighbor. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph

/-- A degree-free formulation convenient for deleting a leaf in an induction. -/
theorem finite_forest_has_leaf {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ x : V, ∀ y z : V, G.Adj x y → G.Adj x z → y = z := by
  classical
  let v : V := Classical.choice inferInstance
  let C := G.connectedComponentMk v
  have htree : C.toSimpleGraph.IsTree := hG.isTree_connectedComponent C
  let : Fintype C := Fintype.ofFinite C
  by_cases hsub : Subsingleton C
  · let : Subsingleton C := hsub
    refine ⟨v, ?_⟩
    intro y z hxy hxz
    have hyv : y = v := congrArg Subtype.val (Subsingleton.elim
      (⟨y, C.mem_supp_of_adj_mem_supp (show v ∈ C from rfl) hxy⟩ : C) ⟨v, rfl⟩)
    exact (hxy.ne hyv.symm).elim
  · let : Nontrivial C := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
    obtain ⟨p, hp, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
    refine ⟨x.val, ?_⟩
    intro y z hxy hxz
    let y' : C := ⟨y, C.mem_supp_of_adj_mem_supp x.property hxy⟩
    let z' : C := ⟨z, C.mem_supp_of_adj_mem_supp x.property hxz⟩
    have hy' : C.toSimpleGraph.Adj x y' := hxy
    have hz' : C.toSimpleGraph.Adj x z' := hxz
    exact congrArg Subtype.val ((huniq y' hy').trans (huniq z' hz').symm)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestRepresentation
namespace OAI

/-! Every finite acyclic graph has a labeled ordered-forest representation. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

universe u

/-- The labels are a permutation of the vertices and adjacency is exactly
parent/child incidence in the ordered forest. -/
theorem exists_forest_representation {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ t : BinaryTree V, (forestNodes t).Nodup ∧ (∀ v, v ∈ forestNodes t) ∧
      ∀ a b, forestAdjacent t a b ↔ G.Adj a b := by
  classical
  suffices h : ∀ n : ℕ, ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (G : SimpleGraph V), G.IsAcyclic →
        ∃ t : BinaryTree V, (forestNodes t).Nodup ∧ (∀ v, v ∈ forestNodes t) ∧
          ∀ a b, forestAdjacent t a b ↔ G.Adj a b by
    exact h _ V rfl G hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst hcard G hG
    by_cases hn : n = 0
    · let : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      exact ⟨.nil, by simp [forestNodes], isEmptyElim, fun a => isEmptyElim a⟩
    · let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨x, hx⟩ := finite_forest_has_leaf G hG
      let W := {v : V // v ≠ x}
      let H : SimpleGraph W := G.comap Subtype.val
      have hW : Fintype.card W < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x := x) (by simp)
      have hH : H.IsAcyclic := hG.of_comap ⟨Subtype.val, Subtype.val_injective⟩
      obtain ⟨t, ht, hcover, hadj⟩ := ih (Fintype.card W) hW W rfl H hH
      let u := t.map (Subtype.val : W → V)
      have hu : (forestNodes u).Nodup := by
        rw [forestNodes_map]
        exact ht.map Subtype.val_injective
      have hnx : x ∉ forestNodes u := by
        rw [forestNodes_map, List.mem_map]
        rintro ⟨v, _, hv⟩
        exact v.property hv
      have hcov (v : V) (hv : v ≠ x) : v ∈ forestNodes u := by
        rw [forestNodes_map]
        exact List.mem_map.mpr ⟨⟨v, hv⟩, hcover _, rfl⟩
      have hOld (a b : V) : forestAdjacent u a b ↔ a ≠ x ∧ b ≠ x ∧ G.Adj a b := by
        constructor
        · intro h
          have hm := forestAdjacent_mem u h
          have ha : a ≠ x := by intro hax; subst a; exact hnx hm.1
          have hb : b ≠ x := by intro hbx; subst b; exact hnx hm.2
          refine ⟨ha, hb, ?_⟩
          have hh := (forestAdjacent_map (Subtype.val : W → V) Subtype.val_injective t
            (⟨a, ha⟩ : W) (⟨b, hb⟩ : W)).mp h
          exact (hadj _ _).mp hh
        · rintro ⟨ha, hb, h⟩
          exact (forestAdjacent_map (Subtype.val : W → V) Subtype.val_injective t
            (⟨a, ha⟩ : W) (⟨b, hb⟩ : W)).mpr ((hadj _ _).mpr h)
      by_cases hneigh : ∃ p, G.Adj x p
      · obtain ⟨p, hxp⟩ := hneigh
        have hp : p ≠ x := hxp.ne.symm
        let s := attachForestLeaf p x u
        have hsperm := attachForestLeaf_nodes_perm p x u hu (hcov p hp)
        refine ⟨s, attachForestLeaf_nodup p x u hu (hcov p hp) hnx, ?_, ?_⟩
        · intro v
          apply hsperm.mem_iff.mpr
          by_cases hv : v = x
          · simp [hv]
          · simp [hcov v hv]
        · intro a b
          rw [attachForestLeaf_adjacent p x u hu (hcov p hp), hOld]
          constructor
          · rintro (⟨_, _, hab⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact hab
            · exact hxp.symm
            · exact hxp
          · intro hab
            by_cases ha : a = x
            · right; right
              subst a
              exact ⟨(hx b p hab hxp), rfl⟩
            · by_cases hb : b = x
              · right; left
                subst b
                exact ⟨hx a p hab.symm hxp, rfl⟩
              · exact Or.inl ⟨ha, hb, hab⟩
      · refine ⟨.node x .nil u, ?_, ?_, ?_⟩
        · simpa only [forestNodes, List.nil_append] using List.nodup_cons.mpr ⟨hnx, hu⟩
        · intro v
          by_cases hv : v = x
          · simp [forestNodes, hv]
          · simp [forestNodes, hcov v hv]
        · intro a b
          simp only [forestAdjacent, forestRoots, List.not_mem_nil, and_false, false_or]
          rw [hOld]
          constructor
          · exact And.right ∘ And.right
          · intro hab
            have ha : a ≠ x := by intro heq; subst a; exact hneigh ⟨b, hab⟩
            have hb : b ≠ x := by intro heq; subst b; exact hneigh ⟨a, hab.symm⟩
            exact ⟨ha, hb, hab⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalForest
namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}


@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestPathCode
namespace OAI

/-! An endpoint pair in a numbered forest recovers an entire non-reversing walk. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The support of a path is transported exactly by a graph isomorphism. -/
theorem forest_path_support_identified (e : G ≃g H) (hH : H.IsAcyclic)
    {a b : V} (p : G.Walk a b) (q : H.Walk (e a) (e b))
    (hp : p.IsPath) (hq : q.IsPath) : p.support.map e = q.support := by
  have heq : p.map e.toHom = q := by
    exact Subtype.mk.inj (hH.subsingleton_path (e a) (e b) |>.elim
      ⟨p.map e.toHom, hp.map e.injective⟩ ⟨q, hq⟩)
  have hh := congrArg SimpleGraph.Walk.support heq
  rw [SimpleGraph.Walk.support_map] at hh
  exact hh

/-- Equal shape and equal endpoint indices determine the same numbered walk,
independently of the numerical realization of the graph. -/
theorem represented_walk_same_code [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hG : ∀ a b, forestAdjacent t a b ↔ G.Adj a b)
    (hH : ∀ a b, forestAdjacent s a b ↔ H.Adj a b)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ()))
    (hGa : G.IsAcyclic) (hHa : H.IsAcyclic)
    {a b : V} (p : G.Walk a b)
    (q : H.Walk (forestShapeEquiv t s ht hc hs hd hshape a)
      (forestShapeEquiv t s ht hc hs hd hshape b))
    (hp : List.IsChain (· ≠ ·) p.edges) (hq : List.IsChain (· ≠ ·) q.edges) :
    p.support.map (fun v => (forestNodes t).idxOf v) =
      q.support.map (fun w => (forestNodes s).idxOf w) := by
  let e := representedGraphIso G H t s ht hc hs hd hG hH hshape
  have hsupport := forest_path_support_identified e hHa p q
    ((hGa.isPath_iff_isChain p).mpr hp) ((hHa.isPath_iff_isChain q).mpr hq)
  calc
    _ = (p.support.map e).map (fun w => (forestNodes s).idxOf w) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      exact (forestShapeEquiv_index t s ht hc hs hd hshape v).symm
    _ = _ := congrArg (List.map (fun w => (forestNodes s).idxOf w)) hsupport

/-- Endpoint indices suffice; the graphs may have different vertex types. -/
theorem represented_walk_same_endpoints [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hG : ∀ a b, forestAdjacent t a b ↔ G.Adj a b)
    (hH : ∀ a b, forestAdjacent s a b ↔ H.Adj a b)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ()))
    (hGa : G.IsAcyclic) (hHa : H.IsAcyclic)
    {a b : V} {c d : W} (p : G.Walk a b) (q : H.Walk c d)
    (hp : List.IsChain (· ≠ ·) p.edges) (hq : List.IsChain (· ≠ ·) q.edges)
    (ha : (forestNodes t).idxOf a = (forestNodes s).idxOf c)
    (hb : (forestNodes t).idxOf b = (forestNodes s).idxOf d) :
    p.support.map (fun v => (forestNodes t).idxOf v) =
      q.support.map (fun w => (forestNodes s).idxOf w) := by
  have hleft : forestShapeEquiv t s ht hc hs hd hshape a = c :=
    preorder_index_injective s hd ((forestShapeEquiv_index t s ht hc hs hd hshape a).trans ha)
  have hright : forestShapeEquiv t s ht hc hs hd hshape b = d :=
    preorder_index_injective s hd ((forestShapeEquiv_index t s ht hc hs hd hshape b).trans hb)
  have h := represented_walk_same_code t s ht hc hs hd hG hH hshape hGa hHa p
    (q.copy hleft.symm hright.symm) hp (by simpa only [Walk.edges_copy] using hq)
  simpa only [Walk.support_copy] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestPathCounting
namespace OAI

/-!
# Counting all realizable numbered path families

The union is over every finite acyclic graph, not a single graph with fixed
numerical coefficients. A typed forest shape and two endpoints per segment
determine the entire family of numbered paths.
-/

namespace TwoPointCorrelations

open _root_.SimpleGraph


namespace ForestPathData

variable {N segments : ℕ}






/-- No numerical vertex label survives in the code. -/
theorem pattern_eq_of_code_eq (d e : ForestPathData N segments) (h : d.code = e.code) :
    d.pattern = e.pattern := by
  have hshape : d.tree.map (fun _ => ()) = e.tree.map (fun _ => ()) := by
    have ht : d.tree.map d.color = e.tree.map e.color :=
      congrArg Subtype.val (congrArg Prod.fst h)
    have hu := congrArg (fun t => t.map (fun _ => ())) ht
    simpa only [← BinaryTree.comp_map, Function.comp_def] using hu
  have hend := congrArg Prod.snd h
  funext i
  apply represented_walk_same_endpoints d.tree e.tree d.nodup d.cover e.nodup e.cover
    d.adjacent e.adjacent hshape d.acyclic e.acyclic (d.walk i) (e.walk i)
    (d.reduced i) (e.reduced i)
  · exact congrArg Fin.val (congrArg Prod.fst (congrFun hend i))
  · exact congrArg Fin.val (congrArg Prod.snd (congrFun hend i))


end ForestPathData





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations


theorem decodeForestPaths_code {N segments : ℕ} (d : ForestPathData N segments) :
    decodeForestPaths d.code = d.pattern := by
  classical
  unfold decodeForestPaths
  split_ifs with h
  · exact ForestPathData.pattern_eq_of_code_eq _ _ h.choose_spec
  · exact (h ⟨d, rfl⟩).elim









@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]


@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBudget
namespace OAI

/-! The actual short-block budgets have the exponent required by the column code. -/

namespace TwoPointCorrelations

open _root_.Filter


/-- The two-half allowance is the final `+2` in the block count. All
remaining constants are absolute, and the exponent is exactly `0.92`. -/
theorem column_budget_bound (L : ℝ) (hL : 1 ≤ L)
    (n s imperfect omittedLabels blocks segments omittedRuns : ℕ)
    (hn : (n : ℝ) ≤ 2 * L)
    (hs : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hI : (imperfect : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hO : (omittedLabels : ℝ) ≤ 2 * L ^ (1 / 50 : ℝ))
    (hB : blocks ≤ n / s + imperfect + 2)
    (hS : segments ≤ (omittedLabels + 1) * blocks)
    (hR : omittedRuns ≤ omittedLabels * blocks) :
    ((2 * segments + omittedRuns + imperfect : ℕ) : ℝ) ≤ 66 * L ^ (0.92 : ℝ) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hspos : (0 : ℝ) < s := (by positivity : (0 : ℝ) < L ^ (1 / 10 : ℝ) / 2).trans_le hs
  have hr : 1 ≤ L ^ (1 / 50 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hd : 1 ≤ L ^ (9 / 10 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hId : (imperfect : ℝ) ≤ 2 * L ^ (9 / 10 : ℝ) := hI.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) (by norm_num))
  have hprod : L ^ (9 / 10 : ℝ) * L ^ (1 / 10 : ℝ) = L := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hdiv : ((n / s : ℕ) : ℝ) ≤ 4 * L ^ (9 / 10 : ℝ) := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ hspos).mpr
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * L ^ (9 / 10 : ℝ) by positivity)
    calc
      (n : ℝ) ≤ 2 * L := hn
      _ = 2 * (L ^ (9 / 10 : ℝ) * L ^ (1 / 10 : ℝ)) := by rw [hprod]
      _ = 4 * L ^ (9 / 10 : ℝ) * (L ^ (1 / 10 : ℝ) / 2) := by ring
      _ ≤ _ := hm
  have hB' : (blocks : ℝ) ≤ 8 * L ^ (9 / 10 : ℝ) := by
    have hb : (blocks : ℝ) ≤ ((n / s : ℕ) : ℝ) + imperfect + 2 := by exact_mod_cast hB
    linarith
  have hS' : (segments : ℝ) ≤ ((omittedLabels : ℝ) + 1) * blocks := by exact_mod_cast hS
  have hR' : (omittedRuns : ℝ) ≤ (omittedLabels : ℝ) * blocks := by exact_mod_cast hR
  have hfactor : 3 * (omittedLabels : ℝ) + 2 ≤ 8 * L ^ (1 / 50 : ℝ) := by linarith
  have hcost : (2 * (segments : ℝ) + omittedRuns + imperfect) ≤
      (3 * (omittedLabels : ℝ) + 2) * blocks + imperfect := by nlinarith
  have hm := mul_le_mul hfactor hB' (Nat.cast_nonneg blocks) (by positivity)
  have hI' : (imperfect : ℝ) ≤ 2 * (L ^ (1 / 50 : ℝ) * L ^ (9 / 10 : ℝ)) := by
    have ht := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hLp.le (9 / 10 : ℝ))
    nlinarith
  have hp : L ^ (1 / 50 : ℝ) * L ^ (9 / 10 : ℝ) = L ^ (0.92 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  push_cast
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnPatternRecovery
namespace OAI

/-! Pass from recovery of canonical names to the universal equality-pattern count. -/

namespace TwoPointCorrelations


theorem column_prefix_pattern_recovers {α : Type*} [DecidableEq α] {n N S O I : ℕ}
    (hn : n ≤ N) (code : ColumnDecoderCode N S O I)
    (label : Fin n → α) (names : Fin n → CanonicalColumnLabel)
    (hprefix : (decodeColumnLabels code).take n = List.ofFn names)
    (heq : ∀ i j, names i = names j ↔ label i = label j) :
    decodeColumnPrefixPattern hn code = fun i j => decide (label i = label j) := by
  have hlookup (i : Fin n) :
      (decodeColumnLabels code).getD i.val (.freshImperfect 0) = names i := by
    have h := congrArg (fun l => l.getD i.val (.freshImperfect 0)) hprefix
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt,
      List.getElem?_ofFn, dif_pos i.isLt, Fin.eta, Option.getD_some] using h
  funext i j
  unfold decodeColumnPrefixPattern decodeColumnPattern
  simp only [Fin.val_castLE, hlookup]
  simp only [heq i j]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnCodeUniverse
namespace OAI

/-! A fixed finite universe for every column with the proved numerical budget. -/

namespace TwoPointCorrelations

open _root_.Filter




/-- The cap depends only on the common scale and forest size, not on the
numerical coefficients, the prime values, or the number of regular lines. -/
theorem budget_column_code_of_counts {n N S O I : ℕ} {L : ℝ}
    (hn : n ≤ N) (hS : S ≤ N) (hO : O ≤ N) (hI : I ≤ N)
    (hcost : ((2 * S + O + I : ℕ) : ℝ) ≤ 66 * L ^ (0.92 : ℝ))
    (code : ColumnDecoderCode N S O I) :
    ∃ full : BudgetColumnCode N L,
      decodeBudgetColumnPattern hn full = decodeColumnPrefixPattern hn code := by
  have htotal : 2 * S + O + I ≤ ⌊66 * L ^ (0.92 : ℝ)⌋₊ := Nat.le_floor hcost
  have hs : S < columnBudgetCap N L + 1 := by
    unfold columnBudgetCap
    omega
  have ho : O < columnBudgetCap N L + 1 := by
    unfold columnBudgetCap
    omega
  have hi : I < columnBudgetCap N L + 1 := by
    unfold columnBudgetCap
    omega
  exact ⟨⟨⟨S, hs⟩, ⟨O, ho⟩, ⟨I, hi⟩, code⟩, rfl⟩






theorem budget_column_array_cover {n J N : ℕ} {L : ℝ} (hn : n ≤ N)
    (pattern : Fin J → Fin n → Fin n → Bool)
    (h : ∀ j, ∃ code : BudgetColumnCode N L, decodeBudgetColumnPattern hn code = pattern j) :
    ∃ code : BudgetColumnArrayCode J N L, decodeBudgetColumnArray hn code = pattern := by
  classical
  choose code hc using h
  exact ⟨code, funext hc⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Unused segment and reference slots are harmless: they only contribute
after the encoded runs have all been emitted. -/
theorem mergeColumnRuns_append (pieces : List (List α ⊕ α))
    (padding : List Bool) (regularTail : List (List α)) (omittedTail : List α) :
    mergeColumnRuns
      (pieces.map (Sum.elim (fun _ => true) (fun _ => false)) ++ padding)
      (pieces.filterMap (Sum.elim some (fun _ => none)) ++ regularTail)
      (pieces.filterMap (Sum.elim (fun _ => none) some) ++ omittedTail) =
        pieces.flatMap (Sum.elim id List.singleton) ++
          mergeColumnRuns padding regularTail omittedTail := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih => cases piece <;>
      simp [mergeColumnRuns, List.filterMap_cons, Sum.elim, List.singleton, ih, List.append_assoc]



@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]

theorem columnRunHeads_length_le (entries : List (Option α)) (previous : Option α) :
    (columnRunHeads entries previous).length ≤ entries.length := by
  induction entries generalizing previous with
  | nil => simp [columnRunHeads]
  | cons a rest ih =>
      cases a with
      | none => simpa only [columnRunHeads, List.length_cons] using (ih none).trans (Nat.le_succ _)
      | some a =>
          simp only [columnRunHeads]
          split_ifs
          · exact (ih (some a)).trans (Nat.le_succ _)
          · simpa only [List.length_cons] using Nat.succ_le_succ (ih (some a))


/-- Extra code slots cannot affect the entries before the padding boundary. -/
theorem expandColumnRuns_take_append (flags padding : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns (flags ++ padding) runs previous).take flags.length =
      expandColumnRuns flags runs previous := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih =>
      rcases flag with ⟨imperfect, boundary⟩
      cases imperfect <;> cases boundary <;> simp [expandColumnRuns, ih]






omit [DecidableEq α] in
/-- Padded flags and references only affect the padded suffix, so a common
code universe can accommodate columns shorter than its vertex bound. -/
theorem attachImperfectLabels_recover_append (full : List (Option CanonicalColumnLabel))
    (label : α → CanonicalColumnLabel) (reference : α → ℕ) (entries : List (α × Bool))
    (padding : List (Option CanonicalColumnLabel)) (referenceTail : List ℕ)
    (hreference : ∀ a ∈ entries, a.2 = false →
      resolveColumnReference full (reference a.1) = label a.1) :
    attachImperfectLabels full (markedColumn label entries ++ padding)
        (imperfectColumnReferences reference entries ++ referenceTail) =
      entries.map (fun a => label a.1) ++ attachImperfectLabels full padding referenceTail := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
      have hr : ∀ b ∈ rest, b.2 = false →
          resolveColumnReference full (reference b.1) = label b.1 :=
        fun b hb => hreference b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨a, perfect⟩
      cases perfect with
      | false =>
          have ha := hreference (a, false) (List.mem_cons_self) rfl
          dsimp only [resolveColumnReference] at ha
          simpa only [markedColumn, imperfectColumnReferences, List.map_cons, List.filterMap_cons,
            Bool.false_eq_true, ↓reduceIte, List.cons_append, attachImperfectLabels,
            List.headD_cons, List.tail_cons, ha] using congrArg (List.cons (label a)) (ih hr)
      | true =>
          simpa only [markedColumn, imperfectColumnReferences, List.map_cons, List.filterMap_cons,
            ↓reduceIte, List.cons_append, attachImperfectLabels] using
              congrArg (List.cons (label a)) (ih hr)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalColumnNames
namespace OAI

/-! Canonical names distinguish precisely the original column's label classes. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α] {N : ℕ}


lemma perfectColumnName_injective : Function.Injective perfectColumnName := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

lemma perfectColumnName_ne_fresh (a : ℕ ⊕ ℕ) (j : ℕ) :
    perfectColumnName a ≠ .freshImperfect j := by
  cases a <;> simp [perfectColumnName]


lemma canonicalColumnName_of_label_eq (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) {i j : Fin N} (h : label i = label j) :
    canonicalColumnName label perfect name i = canonicalColumnName label perfect name j := by
  have hr := (columnRepresentative_eq_iff label perfect i j).mpr h
  simp only [canonicalColumnName, hr]

/-- The only needed naming hypothesis concerns the perfect occurrences.
Fresh imperfect classes are separated by their canonical references. -/
theorem canonicalColumnName_eq_iff (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ)
    (hname : ∀ i ∈ perfect, ∀ j ∈ perfect, name i = name j ↔ label i = label j)
    (i j : Fin N) :
    canonicalColumnName label perfect name i = canonicalColumnName label perfect name j ↔
      label i = label j := by
  constructor
  · intro heq
    let ri := columnRepresentative label perfect i
    let rj := columnRepresentative label perfect j
    change (if ri ∈ perfect then perfectColumnName (name ri) else .freshImperfect ri.val) =
      (if rj ∈ perfect then perfectColumnName (name rj) else .freshImperfect rj.val) at heq
    have hi := columnRepresentative_label label perfect i
    have hj := columnRepresentative_label label perfect j
    by_cases hri : ri ∈ perfect <;> by_cases hrj : rj ∈ perfect
    · rw [if_pos hri, if_pos hrj] at heq
      exact hi.symm.trans (((hname ri hri rj hrj).mp
        (perfectColumnName_injective heq)).trans hj)
    · rw [if_pos hri, if_neg hrj] at heq
      exact (perfectColumnName_ne_fresh _ _ heq).elim
    · rw [if_neg hri, if_pos hrj] at heq
      exact (perfectColumnName_ne_fresh _ _ heq.symm).elim
    · rw [if_neg hri, if_neg hrj] at heq
      have hr : ri = rj := Fin.ext (CanonicalColumnLabel.freshImperfect.inj heq)
      exact hi.symm.trans ((congrArg label hr).trans hj)
  · exact canonicalColumnName_of_label_eq label perfect name


/-- Looking up the canonical representative yields the intended class name,
including when the class has no perfect occurrence. -/
theorem canonical_reference_resolves (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) (i : Fin N) :
    resolveColumnReference (canonicalPerfectEntries label perfect name)
      (columnRepresentative label perfect i).val = canonicalColumnName label perfect name i := by
  let j := columnRepresentative label perfect i
  have hj : j.val < N := j.isLt
  have heq : canonicalColumnName label perfect name j = canonicalColumnName label perfect name i :=
    canonicalColumnName_of_label_eq label perfect name (columnRepresentative_label label perfect i)
  have hget : (canonicalPerfectEntries label perfect name)[j.val]? =
      some (if j ∈ perfect then some (canonicalColumnName label perfect name j) else none) := by
    simp only [canonicalPerfectEntries, List.getElem?_ofFn, dif_pos hj, Fin.eta]
  change ((canonicalPerfectEntries label perfect name)[j.val]?.join).getD
    (.freshImperfect j.val) = _
  rw [hget]
  by_cases hp : j ∈ perfect
  · rw [if_pos hp]
    exact heq
  · rw [if_neg hp]
    change .freshImperfect j.val = canonicalColumnName label perfect name i
    symm
    exact if_neg hp


theorem marked_position_entries (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) :
    markedColumn (canonicalColumnName label perfect name) (columnPositionEntries perfect) =
      canonicalPerfectEntries label perfect name := by
  simp [markedColumn, columnPositionEntries, canonicalPerfectEntries, List.map_ofFn,
    Function.comp_def]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RegularColumnNames
namespace OAI

/-! Name regular perfect classes by forest vertices and omitted classes by occurrences. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α] {n : ℕ}


theorem forestPerfectName_of_label_eq (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i j : Fin n) (h : label i = label j) :
    forestPerfectName label perfect regular number i = forestPerfectName label perfect regular number j := by
  by_cases hi : label i ∈ regular <;> by_cases hj : label j ∈ regular
  · have he : (⟨label i, hi⟩ : regular) = ⟨label j, hj⟩ := Subtype.ext h
    simp only [forestPerfectName, dif_pos hi, dif_pos hj, he]
  · exact (hj (h ▸ hi)).elim
  · exact (hi (h.symm ▸ hj)).elim
  · simp only [forestPerfectName, dif_neg hi, dif_neg hj,
      (columnRepresentative_eq_iff label perfect i j).mpr h]

/-- Injectivity is needed only for lines observed at perfect positions.
No numbering requirement is imposed on unused regular labels. -/
theorem forestPerfectName_eq_iff (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ)
    (hinj : ∀ i ∈ perfect, ∀ j ∈ perfect, ∀ (hi : label i ∈ regular) (hj : label j ∈ regular),
      number ⟨label i, hi⟩ = number ⟨label j, hj⟩ → label i = label j)
    (i : Fin n) (hi : i ∈ perfect) (j : Fin n) (hj : j ∈ perfect) :
    forestPerfectName label perfect regular number i = forestPerfectName label perfect regular number j ↔
      label i = label j := by
  constructor
  · intro heq
    by_cases hir : label i ∈ regular <;> by_cases hjr : label j ∈ regular
    · simp only [forestPerfectName, dif_pos hir, dif_pos hjr, Sum.inl.injEq] at heq
      exact hinj i hi j hj hir hjr heq
    · simp only [forestPerfectName, dif_pos hir, dif_neg hjr, Sum.inl_ne_inr] at heq
    · simp only [forestPerfectName, dif_neg hir, dif_pos hjr, Sum.inr_ne_inl] at heq
    · simp only [forestPerfectName, dif_neg hir, dif_neg hjr, Sum.inr.injEq] at heq
      exact (columnRepresentative_eq_iff label perfect i j).mp (Fin.ext heq)
  · exact forestPerfectName_of_label_eq label perfect regular number i j

/-- The completed names represent the full equality pattern, including
classes having no perfect occurrence. -/
theorem canonical_forest_name_eq_iff (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ)
    (hinj : ∀ i ∈ perfect, ∀ j ∈ perfect, ∀ (hi : label i ∈ regular) (hj : label j ∈ regular),
      number ⟨label i, hi⟩ = number ⟨label j, hj⟩ → label i = label j)
    (i j : Fin n) :
    canonicalColumnName label perfect (forestPerfectName label perfect regular number) i =
      canonicalColumnName label perfect (forestPerfectName label perfect regular number) j ↔ label i = label j := by
  apply canonicalColumnName_eq_iff
  exact forestPerfectName_eq_iff label perfect regular number hinj

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ObservedColumnNames
namespace OAI

/-! Factor canonical occurrence names through the original observed labels. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α] {n : ℕ}


theorem observedColumnName_at (label : Fin n → α) (perfect : Finset (Fin n))
    (name : Fin n → ℕ ⊕ ℕ) (i : Fin n) :
    observedColumnName label perfect name (label i) = canonicalColumnName label perfect name i := by
  classical
  have h : ∃ j, label j = label i := ⟨i, rfl⟩
  simp only [observedColumnName, dif_pos h]
  exact canonicalColumnName_of_label_eq label perfect name h.choose_spec

theorem canonical_forest_name_at_perfect (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i : Fin n) (hi : i ∈ perfect) :
    canonicalColumnName label perfect (forestPerfectName label perfect regular number) i =
      perfectColumnName (forestPerfectName label perfect regular number i) := by
  have hp := columnRepresentative_perfect label perfect i ⟨i, hi, rfl⟩
  rw [canonicalColumnName, if_pos hp]
  exact congrArg perfectColumnName (forestPerfectName_of_label_eq label perfect regular number
    _ i (columnRepresentative_label label perfect i))

/-- On actual perfect regular positions, the canonical class name is the
line number produced by the shared forest. -/
theorem observed_forest_name_regular (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i : Fin n)
    (hi : i ∈ perfect) (hr : label i ∈ regular) :
    observedColumnName label perfect (forestPerfectName label perfect regular number) (label i) =
      .regular (number ⟨label i, hr⟩) := by
  rw [observedColumnName_at, canonical_forest_name_at_perfect label perfect regular number i hi]
  simp only [forestPerfectName, dif_pos hr, perfectColumnName]

/-- Omitted perfect classes carry an occurrence index strictly below the
original column length, independent of any numerical prime value. -/
theorem observed_forest_name_omitted (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i : Fin n)
    (hi : i ∈ perfect) (hr : label i ∉ regular) :
    observedColumnName label perfect (forestPerfectName label perfect regular number) (label i) =
      .omitted (columnRepresentative label perfect i).val := by
  rw [observedColumnName_at, canonical_forest_name_at_perfect label perfect regular number i hi]
  simp only [forestPerfectName, dif_neg hr, perfectColumnName]

theorem observed_forest_name_eq_iff (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ)
    (hinj : ∀ i ∈ perfect, ∀ j ∈ perfect, ∀ (hi : label i ∈ regular) (hj : label j ∈ regular),
      number ⟨label i, hi⟩ = number ⟨label j, hj⟩ → label i = label j)
    (i j : Fin n) :
    observedColumnName label perfect (forestPerfectName label perfect regular number) (label i) =
      observedColumnName label perfect (forestPerfectName label perfect regular number) (label j) ↔
        label i = label j := by
  rw [observedColumnName_at, observedColumnName_at]
  exact canonical_forest_name_eq_iff label perfect regular number hinj i j

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]



@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]

/-- A forced boundary consumes a run label even when the adjacent blocks
end and start with the same label. Arbitrary unused labels remain harmless. -/
theorem expandColumnRuns_cuts_recover (entries : List (Option CanonicalColumnLabel × Bool))
    (previous : Option CanonicalColumnLabel) (tail : List CanonicalColumnLabel) :
    expandColumnRuns (columnFlagsWithCuts entries previous)
      (columnRunHeadsWithCuts entries previous ++ tail) previous = entries.map Prod.fst := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨a, cut⟩
      cases a with
      | none => simpa [columnFlagsWithCuts, columnRunHeadsWithCuts, expandColumnRuns] using
          congrArg (List.cons none) (ih none)
      | some a =>
          cases cut with
          | true =>
              simpa [columnFlagsWithCuts, columnRunHeadsWithCuts, expandColumnRuns] using
                congrArg (List.cons (some a)) (ih (some a))
          | false =>
              by_cases h : previous = some a
              · subst previous
                simpa [columnFlagsWithCuts, columnRunHeadsWithCuts, expandColumnRuns] using
                  congrArg (List.cons (some a)) (ih (some a))
              · simpa [columnFlagsWithCuts, columnRunHeadsWithCuts, h, expandColumnRuns] using
                  congrArg (List.cons (some a)) (ih (some a))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnEncodingRealization
namespace OAI

/-! A full column code from path segments, omitted runs and occurrence references. -/

namespace TwoPointCorrelations





theorem resolveColumnReference_append (full padding : List (Option CanonicalColumnLabel))
    (j : ℕ) (hj : j < full.length) :
    resolveColumnReference (full ++ padding) j = resolveColumnReference full j := by
  simp only [resolveColumnReference, List.getElem?_append_left hj]

/-- The geometric inputs are exact regular path lists and an interleaving
of regular segments with omitted runs. No full equality-pattern or decoder
conclusion is assumed. All unused slots may be padded independently. -/
theorem column_encoding_realization {α : Type*} {N segments omitted imperfect : ℕ} (hN : 0 < N)
    (name : α → CanonicalColumnLabel)
    (pathCode : ForestPathData.Code N segments)
    (entries : List (α × Bool)) (hentries : entries.length ≤ N)
    (cuts : List (Option CanonicalColumnLabel × Bool))
    (hcuts : cuts.map Prod.fst = markedColumn name entries)
    (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel))
    (hpieces : pieces.length ≤ N)
    (regularTail : List (List CanonicalColumnLabel))
    (hregular : List.ofFn (fun i => (evenEntries (decodeForestPaths pathCode i)).map CanonicalColumnLabel.regular) =
      columnPieceRegular pieces ++ regularTail)
    (omittedNames : List (Fin N)) (homittedSize : omittedNames.length ≤ omitted)
    (homitted : columnPieceOmitted pieces =
      omittedNames.map (fun j => CanonicalColumnLabel.omitted j.val))
    (hheads : columnPieceFlatten pieces = columnRunHeadsWithCuts cuts none)
    (reference : α → Fin N)
    (hreferenceSize :
      (entries.filterMap (fun a => if a.2 then none else some (reference a.1))).length ≤ imperfect)
    (hreferenceBound : ∀ a ∈ entries, a.2 = false → (reference a.1).val < entries.length)
    (hreference : ∀ a ∈ entries, a.2 = false →
      resolveColumnReference (markedColumn name entries) (reference a.1).val = name a.1) :
    ∃ code : ColumnDecoderCode N segments omitted imperfect,
      (decodeColumnLabels code).take entries.length = entries.map (fun a => name a.1) := by
  let zero : Fin N := ⟨0, hN⟩
  let marked := markedColumn name entries
  let flags := columnFlagsWithCuts cuts none
  have hflags : flags.length ≤ N := by
    have hc := congrArg List.length hcuts
    simp only [List.length_map, markedColumn] at hc
    simpa only [flags, columnFlagsWithCuts_length] using hc.le.trans hentries
  have hmask : (columnPieceMask pieces).length ≤ N := by
    simpa only [columnPieceMask, List.length_map] using hpieces
  let refs := entries.filterMap (fun a => if a.2 then none else some (reference a.1))
  let code : ColumnDecoderCode N segments omitted imperfect :=
    (pathCode, paddedListCode (columnPieceMask pieces) hmask false,
      paddedListCode flags hflags (false, false),
      paddedListCode omittedNames homittedSize zero,
      paddedListCode refs hreferenceSize zero)
  let omittedTail := (List.replicate (omitted - omittedNames.length) zero).map
    (fun j => CanonicalColumnLabel.omitted j.val)
  let maskPadding := List.replicate (N - (columnPieceMask pieces).length) false
  let extraRuns := mergeColumnRuns maskPadding regularTail omittedTail
  have hpaths : List.ofFn (fun i => (evenEntries (decodeForestPaths code.1 i)).map
      CanonicalColumnLabel.regular) = columnPieceRegular pieces ++ regularTail := by
    change List.ofFn (fun i => (evenEntries (decodeForestPaths pathCode i)).map
      CanonicalColumnLabel.regular) = _
    exact hregular
  have homit : List.ofFn (fun i => CanonicalColumnLabel.omitted (code.2.2.2.1 i).val) =
      columnPieceOmitted pieces ++ omittedTail := by
    change List.ofFn (fun i => CanonicalColumnLabel.omitted
      (paddedListCode omittedNames homittedSize zero i).val) = _
    rw [List.ofFn_comp' (paddedListCode omittedNames homittedSize zero)
      (fun j : Fin N => CanonicalColumnLabel.omitted j.val),
      paddedListCode_ofFn, List.map_append, ← homitted]
  have hruns : mergeColumnRuns (List.ofFn code.2.1)
      (List.ofFn (fun i => (evenEntries (decodeForestPaths code.1 i)).map CanonicalColumnLabel.regular))
      (List.ofFn (fun i => CanonicalColumnLabel.omitted (code.2.2.2.1 i).val)) =
        columnRunHeadsWithCuts cuts none ++ extraRuns := by
    rw [hpaths, homit]
    change mergeColumnRuns (List.ofFn (paddedListCode (columnPieceMask pieces) hmask false)) _ _ = _
    rw [paddedListCode_ofFn]
    have hm := mergeColumnRuns_append pieces maskPadding regularTail omittedTail
    have hm' : mergeColumnRuns (columnPieceMask pieces ++ maskPadding)
        (columnPieceRegular pieces ++ regularTail) (columnPieceOmitted pieces ++ omittedTail) =
        columnPieceFlatten pieces ++ extraRuns := by
      simpa only [columnPieceMask, columnPieceRegular, columnPieceOmitted,
        columnPieceFlatten, extraRuns] using hm
    rw [hheads] at hm'
    exact hm'
  let full := expandColumnRuns (List.ofFn code.2.2.1) (columnRunHeadsWithCuts cuts none ++ extraRuns) none
  have hfullPrefix : full.take entries.length = marked := by
    have ht := expandColumnRuns_take_append flags (List.replicate (N - flags.length) (false, false))
      (columnRunHeadsWithCuts cuts none ++ extraRuns) none
    rw [expandColumnRuns_cuts_recover] at ht
    rw [hcuts] at ht
    change (expandColumnRuns (List.ofFn (paddedListCode flags hflags (false, false)))
      (columnRunHeadsWithCuts cuts none ++ extraRuns) none).take entries.length = marked
    rw [paddedListCode_ofFn]
    have hc : cuts.length = entries.length := by
      have hh := congrArg List.length hcuts
      simpa only [List.length_map, markedColumn] using hh
    simpa only [flags, columnFlagsWithCuts_length, hc, marked] using ht
  have hfull : full = marked ++ full.drop entries.length := by
    rw [← hfullPrefix]
    exact (List.take_append_drop _ _).symm
  have hlookup : ∀ a ∈ entries, a.2 = false →
      resolveColumnReference full (reference a.1).val = name a.1 := by
    intro a ha hp
    rw [hfull, resolveColumnReference_append]
    · exact hreference a ha hp
    · simpa only [marked, markedColumn, List.length_map] using hreferenceBound a ha hp
  have hrefs : List.ofFn (fun i => (code.2.2.2.2 i).val) =
      imperfectColumnReferences (fun a => (reference a).val) entries ++
        (List.replicate (imperfect - refs.length) zero).map Fin.val := by
    change List.ofFn (fun i => (paddedListCode refs hreferenceSize zero i).val) = _
    rw [List.ofFn_comp', paddedListCode_ofFn, List.map_append]
    congr 1
    simp only [refs, imperfectColumnReferences, List.map_filterMap]
    apply List.filterMap_congr
    intro a _
    cases a.2 <;> rfl
  have hatt := attachImperfectLabels_recover_append full name (fun a => (reference a).val)
    entries (full.drop entries.length)
    ((List.replicate (imperfect - refs.length) zero).map Fin.val) hlookup
  refine ⟨code, ?_⟩
  have hdecode : decodeColumnLabels code =
      entries.map (fun a => name a.1) ++ attachImperfectLabels full (full.drop entries.length)
        ((List.replicate (imperfect - refs.length) zero).map Fin.val) := by
    dsimp only [decodeColumnLabels]
    rw [hruns]
    change attachImperfectLabels full full (List.ofFn (fun i => (code.2.2.2.2 i).val)) = _
    rw [hrefs]
    calc
      _ = attachImperfectLabels full (marked ++ full.drop entries.length)
          (imperfectColumnReferences (fun a => (reference a).val) entries ++
            (List.replicate (imperfect - refs.length) zero).map Fin.val) :=
        congrArg (fun l => attachImperfectLabels full l _) hfull
      _ = _ := hatt
  rw [hdecode]
  simpa only [List.length_map] using
    (List.take_left (l₁ := entries.map (fun a => name a.1))
      (l₂ := attachImperfectLabels full (full.drop entries.length)
        ((List.replicate (imperfect - refs.length) zero).map Fin.val)))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalColumnEncoding
namespace OAI

/-! Occurrence representatives recover all equalities involving imperfect positions. -/

namespace TwoPointCorrelations

private theorem reference_filterMap_length {α β : Type*} (reference : α → β)
    (entries : List (α × Bool)) :
    (entries.filterMap (fun a => if a.2 then none else some (reference a.1))).length =
      (entries.filter (fun a => !a.2)).length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨a, flag⟩
      cases flag <;> simp [ih]

/-- Once the regular-path and omitted-run geometry is encoded, all remaining
positions use their proved canonical representatives; no reference lookup
or equality-pattern reconstruction hypothesis is needed. -/
theorem canonical_column_encoding {α : Type*} [DecidableEq α]
    {n N segments omitted imperfect : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (label : Fin n → α) (perfect : Finset (Fin n)) (name : Fin n → ℕ ⊕ ℕ)
    (pathCode : ForestPathData.Code N segments)
    (cuts : List (Option CanonicalColumnLabel × Bool))
    (hcuts : cuts.map Prod.fst = canonicalPerfectEntries label perfect name)
    (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel))
    (hpieces : pieces.length ≤ N)
    (regularTail : List (List CanonicalColumnLabel))
    (hregular : List.ofFn (fun i => (evenEntries (decodeForestPaths pathCode i)).map
      CanonicalColumnLabel.regular) =
        pieces.filterMap (Sum.elim some (fun _ => none)) ++ regularTail)
    (omittedNames : List (Fin N)) (homittedSize : omittedNames.length ≤ omitted)
    (homitted : pieces.filterMap (Sum.elim (fun _ => none) some) =
      omittedNames.map (fun j => CanonicalColumnLabel.omitted j.val))
    (hheads : pieces.flatMap (Sum.elim id List.singleton) = columnRunHeadsWithCuts cuts none)
    (hI : ((columnPositionEntries perfect).filter (fun a => !a.2)).length ≤ imperfect) :
    ∃ code : ColumnDecoderCode N segments omitted imperfect,
      (decodeColumnLabels code).take n = List.ofFn (canonicalColumnName label perfect name) := by
  let reference : Fin n → Fin N := fun i => Fin.castLE hn (columnRepresentative label perfect i)
  have h := column_encoding_realization (imperfect := imperfect) hN (canonicalColumnName label perfect name) pathCode
    (columnPositionEntries perfect) (by simpa [columnPositionEntries] using hn)
    cuts (hcuts.trans (marked_position_entries label perfect name).symm)
    pieces hpieces regularTail hregular omittedNames homittedSize homitted hheads reference
    (by rw [reference_filterMap_length]; exact hI)
    (by intro a _ _; simpa only [reference, columnPositionEntries, List.length_ofFn, Fin.val_castLE] using
      (columnRepresentative label perfect a.1).isLt)
    (by intro a _ _; rw [marked_position_entries]; exact canonical_reference_resolves label perfect name a.1)
  simpa only [columnPositionEntries, List.length_ofFn, List.map_ofFn, Function.comp_def] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestPathRealization
namespace OAI

/-! Arbitrary finite incidence forests fit the coefficient-independent path code. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {N segments : ℕ}

omit [Fintype V] in
lemma list_idxOf_map_injective {W : Type*} [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (l : List V) (v : V) :
    (l.map f).idxOf (f v) = l.idxOf v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases hav : a = v
      · simp [hav]
      · have hfv : f a ≠ f v := fun h => hav (hf h)
        simp only [List.map_cons, List.idxOf_cons_ne _ hfv, List.idxOf_cons_ne _ hav, ih]


theorem forestPathDataOfRepresentation_pattern
    (G : SimpleGraph V) (hG : G.IsAcyclic) (hN : Fintype.card V ≤ N)
    (t : BinaryTree V) (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (ha : ∀ a b, forestAdjacent t a b ↔ G.Adj a b) (color : V → Bool)
    (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges) :
    (forestPathDataOfRepresentation G hG hN t ht hc ha color start finish p hp).pattern =
      fun i => (p i).support.map (fun v => (forestNodes t).idxOf v) := by
  funext i
  simp only [ForestPathData.pattern, forestPathDataOfRepresentation, Walk.support_map,
    forestNodes_map, List.map_map]
  apply List.map_congr_left
  intro v _
  exact list_idxOf_map_injective (Fintype.equivFin V) (Fintype.equivFin V).injective _ v

/-- Every finite forest with boundedly many vertices and any family of
reduced walks contributes to the single universal code universe. -/
theorem forest_paths_realizable (G : SimpleGraph V) (hG : G.IsAcyclic)
    (hN : Fintype.card V ≤ N) (color : V → Bool)
    (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges) :
    ∃ t : BinaryTree V, (forestNodes t).Nodup ∧ (∀ v, v ∈ forestNodes t) ∧
      (fun i => (p i).support.map (fun v => (forestNodes t).idxOf v)) ∈
        Set.range (@ForestPathData.pattern N segments) := by
  obtain ⟨t, ht, hc, ha⟩ := exists_forest_representation G hG
  refine ⟨t, ht, hc, ?_⟩
  exact ⟨forestPathDataOfRepresentation G hG hN t ht hc ha color start finish p hp,
    forestPathDataOfRepresentation_pattern G hG hN t ht hc ha color start finish p hp⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteWalkFamily
namespace OAI

/-! Restricting a finite walk family to its observed vertices preserves its code. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {segments N : ℕ}
  (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))



theorem walkFamilySupport_card_le :
    (walkFamilySupport start finish p).card ≤ ∑ i, (p i).support.length := by
  apply (card_biUnion_le).trans
  exact sum_le_sum (fun i _ => List.toFinset_card_le (p i).support)





theorem restrictedFamilyWalk_reduced (hG : G.IsAcyclic)
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges) (i : Fin segments) :
    List.IsChain (· ≠ ·) (restrictedFamilyWalk start finish p i).edges := by
  have hH := hG.induce (walkFamilySupport start finish p : Set V)
  apply (hH.isPath_iff_isChain _).mp
  apply (Walk.isPath_map_iff_of_injective (f := (Embedding.induce _).toHom)
    (show Function.Injective (Subtype.val : (walkFamilySupport start finish p) → V)
      from Subtype.val_injective)).mp
  have hm : (restrictedFamilyWalk start finish p i).map (Embedding.induce _).toHom = p i :=
    Walk.map_induce (p i) (mem_walkFamilySupport start finish p i)
  rw [hm]
  exact (hG.isPath_iff_isChain _).mpr (hp i)

/-- No finiteness hypothesis on the ambient graph is needed: the observed
support alone suffices for the universal forest code. -/
theorem finite_walk_family_realizable (hG : G.IsAcyclic)
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges)
    (hsize : (∑ i, (p i).support.length) ≤ N) (color : V → Bool) :
    ∃ t : BinaryTree (walkFamilySupport start finish p),
      (forestNodes t).Nodup ∧ (∀ v, v ∈ forestNodes t) ∧
      (fun i => (restrictedFamilyWalk start finish p i).support.map
        (fun v => @List.idxOf _ instBEqOfDecidableEq v (forestNodes t))) ∈
          Set.range (@ForestPathData.pattern N segments) := by
  have hcard : Fintype.card (walkFamilySupport start finish p) ≤ N := by
    rw [Fintype.card_coe]
    exact (walkFamilySupport_card_le start finish p).trans hsize
  exact forest_paths_realizable (walkFamilyGraph start finish p) (hG.induce _) hcard
    (fun v => color v) (walkFamilyStart start finish p) (walkFamilyFinish start finish p)
    (restrictedFamilyWalk start finish p) (restrictedFamilyWalk_reduced start finish p hG hp)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteWalkNumbering
namespace OAI

/-! A single bounded numbering of all vertices observed in a finite walk family. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {segments N : ℕ}

/-- The forest code comes with a numbering of the actual observed vertices.
It is injective across the whole family, so line numbers encode equality
between runs in different segments as well as within each segment. -/
theorem finite_walk_family_numbering
    (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))
    (hG : G.IsAcyclic) (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges)
    (hsize : (∑ i, (p i).support.length) ≤ N) (color : V → Bool) :
    ∃ (number : V → ℕ) (code : ForestPathData.Code N segments),
      Set.InjOn number (walkFamilySupport start finish p : Set V) ∧
      (∀ v ∈ walkFamilySupport start finish p, number v < N) ∧
      ∀ i, decodeForestPaths code i = (p i).support.map number := by
  classical
  obtain ⟨t, ht, hcover, d, hd⟩ := finite_walk_family_realizable start finish p hG hp hsize color
  let index : (walkFamilySupport start finish p) → ℕ :=
    fun v => @List.idxOf _ instBEqOfDecidableEq v (forestNodes t)
  let number : V → ℕ := fun v =>
    if hv : v ∈ walkFamilySupport start finish p then index ⟨v, hv⟩ else 0
  have hnumber (v : walkFamilySupport start finish p) : number v.val = index v := by
    simp only [number, dif_pos v.property]
  have hindex : Function.Injective index := preorder_index_injective t hcover
  have hnodes : (forestNodes t).length ≤ N := by
    rw [forestNodes_length, forest_representation_numNodes t ht hcover, Fintype.card_coe]
    exact (walkFamilySupport_card_le start finish p).trans hsize
  refine ⟨number, d.code, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have heq : index ⟨a, ha⟩ = index ⟨b, hb⟩ := by
      simpa only [← hnumber] using hab
    exact congrArg Subtype.val (hindex heq)
  · intro v hv
    let : BEq (walkFamilySupport start finish p) := instBEqOfDecidableEq
    rw [show number v = index ⟨v, hv⟩ from hnumber ⟨v, hv⟩]
    exact (List.idxOf_lt_length_iff.mpr (hcover ⟨v, hv⟩)).trans_le hnodes
  · intro i
    rw [decodeForestPaths_code]
    have hi := congrFun hd i
    change d.pattern i = (restrictedFamilyWalk start finish p i).support.map index at hi
    rw [hi]
    have hm : (restrictedFamilyWalk start finish p i).map (Embedding.induce _).toHom = p i :=
      Walk.map_induce (p i) (mem_walkFamilySupport start finish p i)
    have hs : (p i).support = (restrictedFamilyWalk start finish p i).support.map
        (fun v => v.val) := by
      exact (congrArg (fun q : G.Walk (start i) (finish i) => q.support) hm).symm.trans
        (Walk.support_map _ _)
    rw [hs, List.map_map]
    apply List.map_congr_left
    intro v _
    exact (hnumber v).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.IncidenceForest
namespace OAI

/-!
# Incidence forests for independent affine directions

An edge is cut by the coordinate of its line direction. All other lines
preserve this coordinate. On the selected line the coordinate determines
the point, so the deleted edge is the only crossing of the cut.
-/

namespace TwoPointCorrelations

open _root_.SimpleGraph

variable {K ι V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Linear coordinates on an independent family, extended to the ambient space. -/
theorem independent_coordinate_functionals [DecidableEq ι] (d : ι → V) (hd : LinearIndependent K d) :
    ∃ φ : ι → V →ₗ[K] K, ∀ i j, φ i (d j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination K d).exists_leftInverse_of_injective
    (linearIndependent_iff_ker.mp hd)
  refine ⟨fun i => (Finsupp.lapply i).comp g, ?_⟩
  intro i j
  have hj := LinearMap.congr_fun hg (Finsupp.single j 1)
  have hdj : g (d j) = Finsupp.single j 1 := by
    simpa only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] using hj
  simp only [LinearMap.comp_apply, Finsupp.lapply_apply, hdj, Finsupp.single_apply]
  simp only [eq_comm]


private theorem coordinate_injective_on_line (anchor d : ι → V)
    (φ : V →ₗ[K] K) (i : ι) (hφ : φ (d i) = 1)
    {x y : V} (hx : ∃ t : K, x = anchor i + t • d i)
    (hy : ∃ t : K, y = anchor i + t • d i) (hxy : φ x = φ y) : x = y := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hst : s = t := by
    simpa only [map_add, map_smul, hφ, smul_eq_mul, mul_one, add_right_inj] using hxy
  rw [hst]


private theorem edgeSide_incidence [DecidableEq ι] (anchor d : ι → V) (φ : V →ₗ[K] K)
    (i : ι) (hφ : ∀ j, φ (d j) = if i = j then 1 else 0)
    (x : V) (hx : ∃ t : K, x = anchor i + t • d i)
    (j : ι) (y : V) (hy : ∃ t : K, y = anchor j + t • d j)
    (hne : ¬ (j = i ∧ y = x)) :
    edgeSide anchor φ i x (.inl j) ↔ edgeSide anchor φ i x (.inr y) := by
  classical
  by_cases hji : j = i
  · subst j
    have hneq : φ y ≠ φ x := by
      intro heq
      exact hne ⟨rfl, coordinate_injective_on_line anchor d φ i (by simpa using hφ i)
        hy hx heq⟩
    simp [edgeSide, hneq]
  · obtain ⟨t, rfl⟩ := hy
    have hdir : φ (d j) = 0 := by simp [hφ, Ne.symm hji]
    simp [edgeSide, hji, map_add, map_smul, hdir]

/-- Every incidence edge is a bridge when line directions are independent. -/
theorem affineIncidenceGraph_edge_isBridge (anchor d : ι → V)
    (hd : LinearIndependent K d) (i : ι) (x : V)
    (hx : ∃ t : K, x = anchor i + t • d i) :
    (affineIncidenceGraph (K := K) anchor d).IsBridge s(Sum.inl i, Sum.inr x) := by
  classical
  obtain ⟨φ, hφ⟩ := independent_coordinate_functionals d hd
  let G := affineIncidenceGraph (K := K) anchor d
  let H := G.deleteEdges {s(Sum.inl i, Sum.inr x)}
  let side := edgeSide anchor (φ i) i x
  have hinv : ∀ {u v}, H.Adj u v → (side u ↔ side v) := by
    intro u v huv
    obtain ⟨huv, hdel⟩ := deleteEdges_adj.mp huv
    have hne : s(u, v) ≠ s(Sum.inl i, Sum.inr x) := by
      simpa only [Set.mem_singleton_iff] using hdel
    cases u with
    | inl j =>
      cases v with
      | inl k => exact huv.elim
      | inr y =>
        apply edgeSide_incidence anchor d (φ i) i (hφ i) x hx j y huv
        rintro ⟨rfl, rfl⟩
        exact hne rfl
    | inr y =>
      cases v with
      | inl j =>
        apply Iff.symm
        apply edgeSide_incidence anchor d (φ i) i (hφ i) x hx j y huv
        rintro ⟨rfl, rfl⟩
        exact hne (by simp only [Sym2.eq_swap])
      | inr z => exact huv.elim
  have hwalk : ∀ {u v} (w : H.Walk u v), side u ↔ side v := by
    intro u v w
    induction w with
    | nil => rfl
    | cons h w ih => exact (hinv h).trans ih
  apply isBridge_iff.mpr
  rintro ⟨w⟩
  have hf := (hwalk w).mpr (show side (Sum.inr x) by rfl)
  exact hf.1 rfl

/-- One affine line per independent direction has an acyclic incidence graph. -/
theorem affineIncidenceGraph_isAcyclic (anchor d : ι → V)
    (hd : LinearIndependent K d) : (affineIncidenceGraph (K := K) anchor d).IsAcyclic := by
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => exact huv.elim
    | inr x => exact affineIncidenceGraph_edge_isBridge anchor d hd i x huv
  | inr x =>
    cases v with
    | inl i =>
      simpa only [Sym2.eq_swap] using affineIncidenceGraph_edge_isBridge anchor d hd i x huv
    | inr y => exact huv.elim


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RegularQuotient
namespace OAI

/-! The low-rank hypothesis produces the regular quotient directions used in forest coding. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule

variable {K α ι : Type*} [Field K] [Fintype α] [Fintype ι]
  [DecidableEq α] [DecidableEq ι]





/-- The algebraic part of forest coding: fewer than `r` independent pairs
leave fewer than `2r` omitted labels; all remaining departures for a label
lie along its independent coordinate direction in the quotient. -/
theorem exists_regular_quotient (label : ι → α) (offset : ι → α → K) (r : ℕ)
    (hno : ∀ S : Finset (EqualLabelPairs label), S.card = r →
      ¬LinearIndependent K (pairFamily (labelPairVectors label offset) S)) :
    ∃ (D : Submodule K (α → K)) (R : Finset α), Rᶜ.card < 2 * r ∧
      LinearIndependent K (fun z : R => D.mkQ (Pi.basisFun K α z)) ∧
      span K (Set.range (fun z : R => D.mkQ (Pi.basisFun K α z))) = ⊤ ∧
      ∀ (z : R) i j, label i = z → label j = z →
        ∃ c : K, D.mkQ (offset i) = D.mkQ (offset j) +
          c • D.mkQ (Pi.basisFun K α z) := by
  classical
  let v := labelPairVectors label offset
  obtain ⟨S, hcard, hind, hdim, hmax⟩ := exists_small_maximal_independent_pairs v r hno
  let D := span K (Set.range (pairFamily v S))
  obtain ⟨R, hRcard, hRind, hRspan⟩ := exists_coordinate_quotient_basis D
  refine ⟨D, R, ?_, hRind, hRspan, ?_⟩
  · rw [hRcard, hdim]
    omega
  · intro z i j hi hj
    let p : EqualLabelPairs label := ⟨(z, i, j), hi, hj⟩
    have hx : D.mkQ (v p 1) ≠ 0 := by
      exact hRind.ne_zero z
    have hpS : p ∉ S := by
      intro hp
      apply hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact subset_span ⟨(⟨p, hp⟩, 1), rfl⟩
    have hpv : v p = ![offset i - offset j, Pi.basisFun K α z] := rfl
    obtain ⟨c, hc⟩ := quotient_line_of_nonextendable_pair (pairFamily v S) hind
      (Pi.basisFun K α z) (offset i - offset j) hx
      (by simpa only [← hpv] using hmax p hpS)
    refine ⟨c, ?_⟩
    rw [map_sub] at hc
    exact sub_eq_iff_eq_add'.mp hc

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FormalDepartures
namespace OAI

/-! Formal departures and exact quotient increments of constant runs. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {K α V : Type*} [Field K] [Fintype α]
  [AddCommGroup V] [Module K V]


theorem formalDeparture_const_run (label : ℕ → α) (coefficient : ℕ → K)
    (a b : ℕ) (hab : a ≤ b) (z : α) (hz : ∀ i ∈ Ico a b, label i = z) :
    formalDeparture label coefficient b = formalDeparture label coefficient a +
      (∑ i ∈ Ico a b, coefficient i) • Pi.basisFun K α z := by
  unfold formalDeparture
  rw [← sum_range_add_sum_Ico _ hab]
  congr 1
  rw [Finset.sum_smul]
  apply sum_congr rfl
  intro i hi
  rw [hz i hi]

/-- Every regular run moves parallel to its independent quotient direction. -/
theorem quotient_departure_const_run (D : Submodule K (α → K))
    (label : ℕ → α) (coefficient : ℕ → K)
    (a b : ℕ) (hab : a ≤ b) (z : α) (hz : ∀ i ∈ Ico a b, label i = z) :
    D.mkQ (formalDeparture label coefficient b) =
      D.mkQ (formalDeparture label coefficient a) +
        (∑ i ∈ Ico a b, coefficient i) • D.mkQ (Pi.basisFun K α z) := by
  rw [formalDeparture_const_run label coefficient a b hab z hz, map_add, map_smul]

theorem affine_line_successor (anchor direction x y : V)
    (hx : ∃ t : K, x = anchor + t • direction)
    (c : K) (hy : y = x + c • direction) :
    ∃ t : K, y = anchor + t • direction := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨t + c, ?_⟩
  rw [hy, add_smul, add_assoc]

theorem nonzero_direction_increment {direction x y : V} {c : K}
    (hd : direction ≠ 0) (hc : c ≠ 0) (hy : y = x + c • direction) : x ≠ y := by
  intro heq
  have hz : c • direction = 0 := by
    have h := hy
    rw [← heq] at h
    exact (add_eq_left.mp h.symm)
  exact (smul_ne_zero hc hd) hz


/-- A regular run has distinct quotient endpoints as required by the
point--line--point non-reversal check. -/
theorem quotient_run_endpoints_ne (D : Submodule K (α → K))
    (label : ℕ → α) (coefficient : ℕ → K)
    (a b : ℕ) (hab : a ≤ b) (z : α) (hz : ∀ i ∈ Ico a b, label i = z)
    (hdir : D.mkQ (Pi.basisFun K α z) ≠ 0)
    (hc : (∑ i ∈ Ico a b, coefficient i) ≠ 0) :
    D.mkQ (formalDeparture label coefficient a) ≠ D.mkQ (formalDeparture label coefficient b) :=
  nonzero_direction_increment hdir hc
    (quotient_departure_const_run D label coefficient a b hab z hz)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RegularLineAnchors
namespace OAI

/-! Choosing one common affine line for all lit occurrences of each regular label. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule

variable {K α ι : Type*} [Field K] [Fintype α] [Fintype ι]
  [DecidableEq α] [DecidableEq ι]

/-- A low-rank family gives independent regular directions and one anchor
per label, shared by every lit departure in every perfect block. -/
theorem exists_regular_line_anchors (label : ι → α) (offset : ι → α → K) (r : ℕ)
    (hno : ∀ S : Finset (EqualLabelPairs label), S.card = r →
      ¬LinearIndependent K (pairFamily (labelPairVectors label offset) S)) :
    ∃ (D : Submodule K (α → K)) (R : Finset α)
      (anchor : R → (α → K) ⧸ D), Rᶜ.card < 2 * r ∧
      LinearIndependent K (fun z : R => D.mkQ (Pi.basisFun K α z)) ∧
      ∀ (z : R) i, label i = z →
        ∃ c : K, D.mkQ (offset i) = anchor z + c • D.mkQ (Pi.basisFun K α z) := by
  classical
  obtain ⟨D, R, hcard, hind, _, hline⟩ := exists_regular_quotient label offset r hno
  let anchor : R → (α → K) ⧸ D := fun z =>
    if h : ∃ i, label i = z then D.mkQ (offset h.choose) else 0
  refine ⟨D, R, anchor, hcard, hind, ?_⟩
  intro z i hi
  have hex : ∃ j, label j = z := ⟨i, hi⟩
  obtain ⟨c, hc⟩ := hline z i hex.choose hi hex.choose_spec
  refine ⟨c, ?_⟩
  simpa only [anchor, dif_pos hex] using hc

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ReducedIncidenceWalk
namespace OAI

/-! Concrete alternating run/transition lists give reduced incidence walks. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph

variable {V : Type*}


theorem walk_reduced_iff_noImmediateReturn {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : List.IsChain (· ≠ ·) p.edges ↔ NoImmediateReturn p.support := by
  induction p with
  | nil => simp [NoImmediateReturn]
  | @cons a b c hab p ih =>
      cases p with
      | nil => simp [NoImmediateReturn]
      | @cons b d c hbd q =>
          have he : s(a, b) ≠ s(b, d) ↔ a ≠ d := by
            simp [hab.ne]
          simp only [Walk.edges_cons, List.isChain_cons_cons, Walk.support_cons] at ih ⊢
          rw [← Walk.cons_tail_support q] at ih ⊢
          exact and_congr he ih

theorem vertex_list_isPath {G : SimpleGraph V} (hG : G.IsAcyclic)
    (l : List V) (hne : l ≠ []) (hchain : l.IsChain G.Adj) (hreturn : NoImmediateReturn l) :
    (Walk.ofSupport l hne hchain).IsPath := by
  apply (hG.isPath_iff_isChain _).mpr
  apply (walk_reduced_iff_noImmediateReturn _).mpr
  simpa only [Walk.support_ofSupport] using hreturn

variable {K ι : Type*} [Field K] [AddCommGroup V] [Module K V]




omit [AddCommGroup V] in
lemma incidenceVertices_ne_nil (i : ι) (steps : List (V × ι)) :
    incidenceVertices i steps ≠ [] := by
  cases steps <;> simp [incidenceVertices]

theorem incidenceVertices_isChain (anchor d : ι → V) (i : ι) (steps : List (V × ι))
    (h : IncidenceChain (K := K) anchor d i steps) :
    (incidenceVertices i steps).IsChain (affineIncidenceGraph (K := K) anchor d).Adj := by
  induction steps generalizing i with
  | nil => exact .singleton _
  | cons step rest ih =>
      rcases step with ⟨x, j⟩
      rcases h with ⟨hi, hj, hrest⟩
      have htail := ih j hrest
      cases rest with
      | nil => exact .cons_cons hi (.cons_cons hj (.singleton _))
      | cons step rest => exact .cons_cons hi (.cons_cons hj htail)

omit [AddCommGroup V] in
theorem incidenceVertices_noImmediateReturn (i : ι) (steps : List (V × ι))
    (h : IncidenceReduced i steps) : NoImmediateReturn (incidenceVertices i steps) := by
  induction steps generalizing i with
  | nil => trivial
  | cons step rest ih =>
      rcases step with ⟨x, j⟩
      rcases h with ⟨hij, hpoint, hrest⟩
      have htail := ih j hrest
      cases rest with
      | nil => simpa [incidenceVertices, NoImmediateReturn] using hij
      | cons step rest =>
          rcases step with ⟨y, k⟩
          have hxy : x ≠ y := hpoint y k rfl
          change (Sum.inl i : ι ⊕ V) ≠ Sum.inl j ∧
            (Sum.inr x : ι ⊕ V) ≠ Sum.inr y ∧ _
          exact ⟨fun h => hij (Sum.inl.inj h), fun h => hxy (Sum.inr.inj h), htail⟩

/-- The actual alternating incidence walk is simple. In particular, its
line sequence is determined by its two endpoints in the forest. -/
theorem incidence_vertices_simple (anchor d : ι → V) (hd : LinearIndependent K d)
    (i : ι) (steps : List (V × ι))
    (hc : IncidenceChain (K := K) anchor d i steps) (hr : IncidenceReduced i steps) :
    (Walk.ofSupport (incidenceVertices i steps) (incidenceVertices_ne_nil i steps)
      (incidenceVertices_isChain anchor d i steps hc)).IsPath :=
  vertex_list_isPath (affineIncidenceGraph_isAcyclic anchor d hd) _ _ _
    (incidenceVertices_noImmediateReturn i steps hr)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.IncidenceDecoding
namespace OAI

/-! The regular-part decoder recovers the original run labels. -/

namespace TwoPointCorrelations

variable {ι V W : Type*}

theorem incidenceVertices_length (i : ι) (steps : List (V × ι)) :
    (incidenceVertices i steps).length = 2 * steps.length + 1 := by
  induction steps generalizing i with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨x, j⟩
      simp only [incidenceVertices, List.length_cons, ih]
      omega

/-- Taking even entries removes transition points and retains exactly
the line vertex for each run, also after assigning canonical numbers. -/
theorem evenEntries_incidenceVertices (f : ι ⊕ V → W) (i : ι) (steps : List (V × ι)) :
    evenEntries ((incidenceVertices i steps).map f) =
      (i :: steps.map Prod.snd).map (fun j => f (.inl j)) := by
  induction steps generalizing i with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨x, j⟩
      simpa only [incidenceVertices, List.map_cons, evenEntries] using
        congrArg (fun l => f (.inl i) :: l) (ih j)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuotientRunPaths
namespace OAI

/-! Constant perfect runs give the concrete reduced paths used by column coding. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.SimpleGraph

variable {K α ι : Type*} [Field K] [Fintype α]



/-- Both adjacent lines contain the exact common departure at a transition. -/
theorem quotientRunData_incidenceChain (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K) (a : ℕ) (i : ι) (steps : List (ℕ × ι))
    (hstart : ∃ c : K, D.mkQ (formalDeparture label coefficient a) = anchor i +
      c • D.mkQ (Pi.basisFun K α (regularLabel i)))
    (hdata : QuotientRunData D anchor regularLabel label coefficient a i steps) :
    IncidenceChain (K := K) anchor (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))) i
      (quotientRunSteps D label coefficient steps) := by
  induction steps generalizing a i with
  | nil => trivial
  | cons step rest ih =>
      rcases step with ⟨b, j⟩
      rcases hdata with ⟨hab, hconst, _, _, hnext, hrest⟩
      refine ⟨?_, hnext, ih b j hnext hrest⟩
      exact affine_line_successor _ _ _ _ hstart _
        (quotient_departure_const_run D label coefficient a b hab (regularLabel i) hconst)

/-- Nonzero numerical runs prohibit point--line--point reversal; distinct
adjacent run labels prohibit line--point--line reversal. -/
theorem quotientRunData_reduced (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K)
    (hdir : ∀ j, D.mkQ (Pi.basisFun K α (regularLabel j)) ≠ 0)
    (a : ℕ) (i : ι) (steps : List (ℕ × ι))
    (hdata : QuotientRunData D anchor regularLabel label coefficient a i steps) :
    IncidenceReduced i (quotientRunSteps D label coefficient steps) := by
  induction steps generalizing a i with
  | nil => trivial
  | cons step rest ih =>
      rcases step with ⟨b, j⟩
      rcases hdata with ⟨_, _, _, hij, _, hrest⟩
      refine ⟨hij, ?_, ih b j hrest⟩
      intro y k hhead
      cases rest with
      | nil => simp at hhead
      | cons step rest =>
          rcases step with ⟨c, l⟩
          simp only [List.map_cons, List.head?_cons, Option.some.injEq,
            Prod.mk.injEq] at hhead
          rcases hhead with ⟨rfl, rfl⟩
          rcases hrest with ⟨hbc, hconst, hnonzero, _, _, _⟩
          exact quotient_run_endpoints_ne D label coefficient b c hbc (regularLabel j)
            hconst (hdir j) hnonzero

/-- The path support consists of exactly the canonical regular run lines
alternating with their actual transition departures. -/
theorem quotientRunData_simple (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K)
    (hind : LinearIndependent K (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))))
    (a : ℕ) (i : ι) (steps : List (ℕ × ι))
    (hstart : ∃ c : K, D.mkQ (formalDeparture label coefficient a) = anchor i +
      c • D.mkQ (Pi.basisFun K α (regularLabel i)))
    (hdata : QuotientRunData D anchor regularLabel label coefficient a i steps) :
    (Walk.ofSupport (incidenceVertices i (quotientRunSteps D label coefficient steps))
      (incidenceVertices_ne_nil _ _)
      (incidenceVertices_isChain anchor _ _ _
        (quotientRunData_incidenceChain D anchor regularLabel label coefficient a i steps hstart hdata))).IsPath := by
  exact incidence_vertices_simple anchor _ hind i _
    (quotientRunData_incidenceChain D anchor regularLabel label coefficient a i steps hstart hdata)
    (quotientRunData_reduced D anchor regularLabel label coefficient
      (fun j => hind.ne_zero j) a i steps hdata)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations


namespace SignedStep


@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]



@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]

lemma divisor_dvd_displacement (h : ℕ) (a : SignedStep) : a.divisor ∣ a.displacement h := by
  refine ⟨(if a.forward then 1 else -1) * (h : ℤ), ?_⟩
  simp only [divisor, displacement]
  ring

@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl

lemma divisor_dvd_arrival (h : ℕ) (a : SignedStep) (x : ℤ) (hx : a.divisor ∣ x) :
    a.divisor ∣ x + a.displacement h := hx.add (a.divisor_dvd_displacement h)

/-- The exclusions on the common multiplier, padding, and tuple imply the
exact absence of this prime from the integer displacement. -/
lemma prime_not_dvd_displacement (h p : ℕ) (hp : p.Prime) (a : SignedStep)
    (hh : ¬p ∣ h) (hq : ¬p ∣ a.padding) (hd : ¬p ∣ a.tuple) :
    ¬(p : ℤ) ∣ a.displacement h := by
  have hn : ¬p ∣ h * a.padding * a.tuple := hp.not_dvd_mul (hp.not_dvd_mul hh hq) hd
  have hi : ¬(p : ℤ) ∣ ((h * a.padding * a.tuple : ℕ) : ℤ) := by exact_mod_cast hn
  rcases a with ⟨b, d, q⟩
  cases b <;> simpa [displacement, Int.natCast_mul, mul_assoc] using hi

end SignedStep


@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]


@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl

lemma positiveWord_append (h : ℕ) (x : ℤ) (u v : List SignedStep) :
    PositiveWord h x (u ++ v) ↔
      PositiveWord h x u ∧ PositiveWord h (x + wordDisplacement h u) v := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
      simp only [List.cons_append, positiveWord_cons, ih, wordDisplacement_cons]
      simp only [add_assoc, and_assoc]

/-- Positivity at arrivals makes reversed paths positive at their old endpoint. -/
lemma PositiveWord.reverse {h : ℕ} {x : ℤ} {w : List SignedStep} (hw : PositiveWord h x w) :
    PositiveWord h (x + wordDisplacement h w) (reverseWord w) := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
      rcases hw with ⟨ha, hw⟩
      rw [reverseWord_cons, positiveWord_append]
      constructor
      · simpa only [wordDisplacement_cons, add_assoc] using ih hw
      · have hav := a.divisor_dvd_arrival h x ha
        simpa [PositiveWord, wordDisplacement_cons, add_assoc] using hav


lemma WordVertex.reverse {h : ℕ} {x y : ℤ} {w : List SignedStep}
    (hy : WordVertex h (x + wordDisplacement h w) (reverseWord w) y) :
    WordVertex h x w y := by
  obtain ⟨u, v, huv, hy⟩ := hy
  have hsplit : w = reverseWord v ++ reverseWord u := by
    simpa only [reverseWord_reverseWord, reverseWord_append] using congrArg reverseWord huv
  refine ⟨reverseWord v, reverseWord u, hsplit, ?_⟩
  have hsum := congrArg (wordDisplacement h) huv
  simp only [wordDisplacement_reverseWord, wordDisplacement_append] at hsum ⊢
  omega

lemma PositiveWord.infix {h : ℕ} {x : ℤ} {u w : List SignedStep}
    (hw : PositiveWord h x w) (hu : u <:+: w) :
    ∃ y, WordVertex h x w y ∧ PositiveWord h y u := by
  obtain ⟨a, b, hab⟩ := hu
  have hpositive : PositiveWord h x (a ++ (u ++ b)) := by
    rw [← hab] at hw
    simpa only [List.append_assoc] using hw
  obtain ⟨_, hub⟩ := (positiveWord_append h x a (u ++ b)).mp hpositive
  refine ⟨x + wordDisplacement h a, ⟨a, u ++ b, by simpa only [List.append_assoc] using hab.symm, rfl⟩,
    ((positiveWord_append h (x + wordDisplacement h a) u b).mp hub).1⟩


lemma OrientedInfix.refl (w : List SignedStep) : OrientedInfix w w := Or.inl (List.infix_refl _)

lemma reverseWord_infix {u w : List SignedStep} (hu : u <:+: w) :
    reverseWord u <:+: reverseWord w := hu.reverse.map SignedStep.flip

lemma OrientedInfix.trans {u v w : List SignedStep}
    (hu : OrientedInfix u v) (hv : OrientedInfix v w) : OrientedInfix u w := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact Or.inl (hu.trans hv)
  · exact Or.inr (hu.trans hv)
  · exact Or.inr (hu.trans (reverseWord_infix hv))
  · exact Or.inl (hu.trans (by simpa using reverseWord_infix hv))


lemma PositiveWord.orientedInfix {h : ℕ} {x : ℤ} {u w : List SignedStep}
    (hw : PositiveWord h x w) (hu : OrientedInfix u w) :
    ∃ y, WordVertex h x w y ∧ PositiveWord h y u := by
  rcases hu with hu | hu
  · exact hw.infix hu
  · obtain ⟨y, hy, hu⟩ := hw.reverse.infix hu
    exact ⟨y, hy.reverse, hu⟩


/-- Strictly decreasing lengths give a minimal prohibited contiguous word. -/
theorem exists_minimal_orientedInfix (P : List SignedStep → Prop) (w : List SignedStep)
    (hw : P w) : ∃ u, OrientedInfix u w ∧ MinimalWord P u := by
  classical
  have hex : ∃ n : ℕ, ∃ u, OrientedInfix u w ∧ u.length = n ∧ P u :=
    ⟨w.length, w, OrientedInfix.refl w, rfl, hw⟩
  obtain ⟨u, hu, hlen, hP⟩ := Nat.find_spec hex
  refine ⟨u, hu, hP, ?_⟩
  intro v hv hlt hPv
  have hmin := Nat.find_min' hex ⟨v, hv.trans hu, rfl, hPv⟩
  omega








/-- The same deletion excludes prohibited words contained in the path in
either orientation, by composing the two stages of witness descent. -/
theorem PositiveWord.not_prohibited_orientedInfix {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {x : ℤ} {u w : List SignedStep} (hw : PositiveWord h x w)
    (hsurvive : ∀ y, WordVertex h x w y → ¬ProhibitedSite h s supply y)
    (hu : OrientedInfix u w) : ¬ForwardProhibited h s supply u := by
  intro hpro
  obtain ⟨v, hv, hmin⟩ := exists_minimal_orientedInfix (ForwardProhibited h s supply) u hpro
  obtain ⟨y, hy, hpositive⟩ := hw.orientedInfix (hv.trans hu)
  exact hsurvive y hy ⟨v, hpositive, hmin⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockGeometry
namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open _root_.Finset



lemma not_occurrenceIntervals_iff {α : Type*} (P : α → ℕ → Prop) (n : ℕ) :
    ¬OccurrenceIntervals P 0 n ↔ ∃ p i j, OccurrenceHole P n p i j := by
  classical
  constructor
  · intro h
    simp only [OccurrenceIntervals, not_forall] at h
    obtain ⟨p, i, k, j, h⟩ := h
    obtain ⟨_, hik, hkj, hjn, hpi, hpj, hpk⟩ := h
    have hik' : i < k := lt_of_le_of_ne hik (fun heq => hpk (heq ▸ hpi))
    have hkj' : k < j := lt_of_le_of_ne hkj (fun heq => hpk (heq.symm ▸ hpj))
    exact ⟨p, i, j, hik'.trans hkj', hjn, hpi, hpj, k, hik', hkj', hpk⟩
  · rintro ⟨p, i, j, hij, hjn, hpi, hpj, k, hik, hkj, hpk⟩ h
    exact hpk (h p i k j (Nat.zero_le _) hik.le hkj.le hjn hpi hpj)

/-- A shortest gap has no appearances of its own label in its interior, and
all labels have interval-shaped appearances before its returning endpoint. -/
theorem exists_shortest_occurrence_hole {α : Type*} (P : α → ℕ → Prop) (n : ℕ)
    (h : ¬OccurrenceIntervals P 0 n) :
    ∃ p i j, OccurrenceHole P n p i j ∧
      (∀ k, i < k → k < j → ¬P p k) ∧ OccurrenceIntervals P i j := by
  classical
  obtain ⟨p, i, j, hgap⟩ := (not_occurrenceIntervals_iff P n).mp h
  have hex : ∃ d : ℕ, ∃ p i j, OccurrenceHole P n p i j ∧ j - i = d :=
    ⟨j - i, p, i, j, hgap, rfl⟩
  obtain ⟨p, i, j, hgap, hlength⟩ := Nat.find_spec hex
  have hmin (q : α) (u v : ℕ) (huv : OccurrenceHole P n q u v) : j - i ≤ v - u := by
    have h := Nat.find_min' hex ⟨q, u, v, huv, rfl⟩
    omega
  rcases hgap with ⟨hij, hjn, hpi, hpj, r, hir, hrj, hpr⟩
  refine ⟨p, i, j, ⟨hij, hjn, hpi, hpj, r, hir, hrj, hpr⟩, ?_, ?_⟩
  · intro k hik hkj hpk
    rcases lt_trichotomy r k with hrk | hrk | hrk
    · have h := hmin p i k ⟨hik, hkj.trans hjn, hpi, hpk, r, hir, hrk, hpr⟩
      omega
    · exact hpr (hrk ▸ hpk)
    · have h := hmin p k j ⟨hkj, hjn, hpk, hpj, r, hrk, hrj, hpr⟩
      omega
  · intro q a b c hia hab hbc hcj hqa hqc
    by_contra hqb
    have hab' : a < b := lt_of_le_of_ne hab (fun heq => hqb (heq ▸ hqa))
    have hbc' : b < c := lt_of_le_of_ne hbc (fun heq => hqb (heq.symm ▸ hqc))
    have h := hmin q a c ⟨hab'.trans hbc', hcj.trans hjn, hqa, hqc, b, hab', hbc', hqb⟩
    omega


lemma intervalDisplacement_eq_sub (D : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    intervalDisplacement D a b = (∑ i ∈ range b, D i) - ∑ i ∈ range a, D i :=
  sum_Ico_eq_sub D hab

lemma intervalDisplacement_cons (D : ℕ → ℤ) {a b : ℕ} (hab : a < b) :
    intervalDisplacement D a b = D a + intervalDisplacement D (a + 1) b := by
  rw [intervalDisplacement_eq_sub D hab.le,
    intervalDisplacement_eq_sub D (by omega), sum_range_succ]
  ring

@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]


/-- Positivity at two departures supplies the divisibility of the intervening
sum, with no assertion of independence between the sites. -/
lemma departure_difference_dvd {α : Type*} (P : α → ℕ → Prop) (D : ℕ → ℤ)
    (prime : α → ℕ) (x : ℤ) (n : ℕ)
    (hpositive : ∀ p i, i < n → P p i → (prime p : ℤ) ∣ x + ∑ a ∈ range i, D a)
    {p : α} {i j : ℕ} (hij : i ≤ j) (hj : j < n) (hi : P p i) (hjP : P p j) :
    (prime p : ℤ) ∣ intervalDisplacement D i j := by
  have hleft := hpositive p i (lt_of_le_of_lt hij hj) hi
  have hright := hpositive p j hj hjP
  have hsub := hright.sub hleft
  rw [intervalDisplacement_eq_sub D hij]
  convert (preTransparency := .instances) hsub using 1; ring

/-- The shortest returning prime would give a prohibited subword. Thus a
positive block avoiding those words has interval-shaped prime occurrences. -/
theorem block_occurrence_intervals {α : Type*} (P : α → ℕ → Prop) (D : ℕ → ℤ)
    (prime : α → ℕ) (x : ℤ) (n : ℕ)
    (hpositive : ∀ p i, i < n → P p i → (prime p : ℤ) ∣ x + ∑ a ∈ range i, D a)
    (hon : ∀ p i, i < n → P p i → (prime p : ℤ) ∣ D i)
    (hoff : ∀ p i, (∃ j, j < n ∧ P p j) → i < n → ¬P p i → ¬(prime p : ℤ) ∣ D i)
    (havoid : ∀ a b, b ≤ n → ¬ProhibitedInterval P D prime a b) :
    OccurrenceIntervals P 0 n := by
  classical
  by_contra h
  obtain ⟨p, i, j, hhole, hgap, hlocal⟩ := exists_shortest_occurrence_hole P n h
  obtain ⟨hij, hjn, hpi, hpj, k, hik, hkj, _⟩ := hhole
  have hsum := departure_difference_dvd P D prime x n hpositive hij.le hjn hpi hpj
  have hfirst := hon p i (hij.trans hjn) hpi
  have htail : (prime p : ℤ) ∣ intervalDisplacement D (i + 1) j := by
    rw [intervalDisplacement_cons D hij] at hsum
    have hd := hsum.sub hfirst
    convert (preTransparency := .instances) hd using 1; ring
  have hlength : i + 2 < j := by
    by_contra hlen
    have heq : j = i + 2 := by omega
    subst j
    rw [show i + 2 = (i + 1) + 1 by omega, intervalDisplacement_singleton] at htail
    exact hoff p (i + 1) ⟨i, by omega, hpi⟩ (by omega) (hgap (i + 1) (by omega) (by omega)) htail
  apply havoid i j hjn.le
  exact ⟨hlength, hlocal, p, hpi, hgap (j - 1) (by omega) (by omega),
    i + 1, by omega, by omega, htail⟩

/-- Once occurrences are intervals, a directed change in the first two
prime tuples supplies a prime absent from the final tuple. Any zero sum
then gives the same prohibited suffix relation. -/
theorem block_nonzero_subintervals {α : Type*} (P : α → ℕ → Prop) (D : ℕ → ℤ)
    (prime : α → ℕ) (n : ℕ) (hinterval : OccurrenceIntervals P 0 n)
    (hon : ∀ p i, i < n → P p i → (prime p : ℤ) ∣ D i)
    (hoff : ∀ p i, (∃ j, j < n ∧ P p j) → i < n → ¬P p i → ¬(prime p : ℤ) ∣ D i)
    (hstep : ∀ i, i < n → D i ≠ 0)
    (hchange : ∀ i, i + 1 < n → ∃ p, P p i ∧ ¬P p (i + 1))
    (havoid : ∀ a b, b ≤ n → ¬ProhibitedInterval P D prime a b) :
    ∀ a b, a < b → b ≤ n → intervalDisplacement D a b ≠ 0 := by
  intro a b hab hbn hzero
  by_cases hshort : b = a + 1
  · subst b
    exact hstep a (by omega) (by simpa using hzero)
  have hab2 : a + 1 < b := by omega
  obtain ⟨p, hpa, hpnext⟩ := hchange a (by omega)
  have hplast : ¬P p (b - 1) := by
    intro hp
    exact hpnext (hinterval p a (a + 1) (b - 1) (Nat.zero_le _) (by omega)
      (by omega) (by omega) hpa hp)
  have htail : (prime p : ℤ) ∣ intervalDisplacement D (a + 1) b := by
    have hfirst := hon p a (by omega) hpa
    rw [intervalDisplacement_cons D hab] at hzero
    have heq : intervalDisplacement D (a + 1) b = -D a := by omega
    rw [heq]
    exact hfirst.neg_right
  by_cases htwo : b = a + 2
  · subst b
    rw [show a + 2 = (a + 1) + 1 by omega, intervalDisplacement_singleton] at htail
    exact hoff p (a + 1) ⟨a, by omega, hpa⟩ (by omega) hpnext htail
  apply havoid a b hbn
  refine ⟨by omega, ?_, p, hpa, hplast, a + 1, by omega, by omega, htail⟩
  intro q i j k hai hij hjk hkb hqi hqk
  exact hinterval q i j k (by omega) hij hjk (by omega) hqi hqk

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RunSegments
namespace OAI

/-! Interval-shaped label uses bound omitted runs and regular segments. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- A sequence obtained by keeping run starts has no repeated label when
every label's original occurrences form an interval. -/
theorem run_labels_injective {m n : ℕ} (label : Fin n → α)
    (hinterval : ∀ i j k : Fin n, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (start : Fin m → Fin n) (hstart : StrictMono start)
    (hchange : ∀ i j : Fin m, i.val + 1 = j.val → label (start i) ≠ label (start j)) :
    Function.Injective (label ∘ start) := by
  have hless : ∀ i j : Fin m, i < j → label (start i) ≠ label (start j) := by
    intro i j hij heq
    let next : Fin m := ⟨i.val + 1, by omega⟩
    have hinext : i ≤ next := by change i.val ≤ i.val + 1; omega
    have hnextj : next ≤ j := by change i.val + 1 ≤ j.val; exact hij
    have hn := hinterval (start i) (start next) (start j)
      (hstart.monotone hinext) (hstart.monotone hnextj) heq
    exact hchange i next rfl hn.symm
  intro i j heq
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (hless i j hij heq).elim
  · exact hij
  · exact (hless j i hji heq.symm).elim









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CompressedRuns
namespace OAI

/-! Actual constant-run compression of a perfect block. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

/-- The decoder's greedy run heads are exactly the library's constant-run
compression, so its sublist and adjacent-inequality properties apply. -/
theorem destutter'_eq_columnRunHeads (a : α) (l : List α) :
    l.destutter' (· ≠ ·) a = a :: columnRunHeads (l.map some) (some a) := by
  induction l generalizing a with
  | nil => rfl
  | cons b rest ih =>
      by_cases h : a = b
      · subst b
        simpa [List.destutter', columnRunHeads] using ih a
      · simpa [List.destutter', columnRunHeads, h] using congrArg (List.cons a) (ih b)

theorem columnRunHeads_eq_destutter (l : List α) :
    columnRunHeads (l.map some) none = l.destutter (· ≠ ·) := by
  cases l with
  | nil => rfl
  | cons a rest =>
      rw [List.destutter_cons', destutter'_eq_columnRunHeads]
      simp [columnRunHeads]

omit [DecidableEq α] in
/-- A subsequence with unequal adjacent entries has no repeated label when
all occurrences in the original block are interval-shaped. -/
theorem sublist_chain_nodup_of_intervals (l runs : List α) (hsub : runs.Sublist l)
    (hchain : runs.IsChain (· ≠ ·))
    (hinterval : ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) : runs.Nodup := by
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
  have hchange : ∀ i j : Fin runs.length, i.val + 1 = j.val → l.get (e i) ≠ l.get (e j) := by
    intro i j hij
    rw [← he i, ← he j]
    have hj : i.val + 1 < runs.length := by omega
    have hc := (List.isChain_iff_getElem.mp hchain) i.val hj
    simpa only [List.get_eq_getElem, hij] using hc
  have hinj := run_labels_injective l.get hinterval e e.strictMono hchange
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  apply hinj
  change l.get (e i) = l.get (e j)
  rw [← he i, ← he j, hij]

/-- Each numerical label contributes at most one compressed run in a
perfect block. This is proved for the actual run-head algorithm. -/
theorem columnRunHeads_nodup (l : List α)
    (hinterval : ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) :
    (columnRunHeads (l.map some) none).Nodup := by
  rw [columnRunHeads_eq_destutter]
  exact sublist_chain_nodup_of_intervals l _ (List.destutter_sublist (R := (· ≠ ·)) l)
    (List.isChain_destutter (R := (· ≠ ·)) l) hinterval

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RunCoverage
namespace OAI

/-! Every observed regular class is present in an encoded regular segment. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

/-- Greedy compression can suppress only the preceding label; no observed
class disappears from the previous-label/run-head pair. -/
theorem columnRunHeads_cover (l : List α) (previous : Option α) (a : α) (ha : a ∈ l) :
    previous = some a ∨ a ∈ columnRunHeads (l.map some) previous := by
  induction l generalizing previous with
  | nil => simp at ha
  | cons b rest ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · by_cases hp : previous = some a
        · exact Or.inl hp
        · exact Or.inr (by simp [columnRunHeads, hp])
      · rcases ih (some b) ha with heq | hm
        · have hab : b = a := Option.some.inj heq
          subst b
          by_cases hp : previous = some a
          · exact Or.inl hp
          · exact Or.inr (by simp [columnRunHeads, hp])
        · exact Or.inr (by
            simp only [List.map_cons, columnRunHeads]
            split_ifs <;> simp [hm])

theorem mem_columnRunHeads (l : List α) (a : α) (ha : a ∈ l) :
    a ∈ columnRunHeads (l.map some) none := by
  exact (columnRunHeads_cover l none a ha).resolve_left (by simp)

omit [DecidableEq α] in
/-- A regular observed run occurs in one of the actual regular pieces,
so the shared forest numbering applies to it. -/
theorem partitionColumnRuns_regular_cover (omitted : α → Bool) (runs : List α)
    (a : α) (ha : a ∈ runs) (hregular : omitted a = false) :
    ∃ segment, Sum.inl segment ∈ partitionColumnRuns omitted runs ∧ a ∈ segment := by
  have hflat : a ∈ (partitionColumnRuns omitted runs).flatMap (Sum.elim id List.singleton) := by
    rwa [partitionColumnRuns_flatten]
  obtain ⟨piece, hp, ha⟩ := List.mem_flatMap.mp hflat
  cases piece with
  | inl segment => exact ⟨segment, hp, ha⟩
  | inr b =>
      have hab : a = b := List.mem_singleton.mp ha
      subst b
      have hm : a ∈ (partitionColumnRuns omitted runs).filterMap (Sum.elim (fun _ => none) some) :=
        List.mem_filterMap.mpr ⟨.inr a, hp, rfl⟩
      rw [partitionColumnRuns_omitted] at hm
      have ht := (List.mem_filter.mp hm).2
      simp [hregular] at ht

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunks
namespace OAI

/-! Cutting actual perfect blocks and preserving their exact run lists. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]


/-- Streaming run compression composes at any cut, including imperfect entries. -/
theorem columnRunHeadsWithCuts_append (l r : List (Option α × Bool)) (previous : Option α) :
    columnRunHeadsWithCuts (l ++ r) previous =
      columnRunHeadsWithCuts l previous ++
        columnRunHeadsWithCuts r (columnFinalState l previous) := by
  induction l generalizing previous with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨a, cut⟩
      cases a with
      | none => simpa [columnRunHeadsWithCuts, columnFinalState] using ih none
      | some a =>
          simp only [List.cons_append, columnRunHeadsWithCuts, columnFinalState]
          split_ifs <;> simp only [ih, List.cons_append]


theorem plainBlock_heads (l : List α) (previous : Option α) :
    columnRunHeadsWithCuts (l.map (fun a => (some a, false))) previous =
      columnRunHeads (l.map some) previous := by
  induction l generalizing previous with
  | nil => rfl
  | cons a rest ih =>
      by_cases h : previous = some a <;> simp [columnRunHeadsWithCuts, columnRunHeads, h, ih]

/-- A perfect block has its usual compressed run list regardless of the
label just before it. Thus equal labels across block boundaries stay distinct runs. -/
theorem perfectBlockCuts_heads (l : List α) (previous : Option α) :
    columnRunHeadsWithCuts (perfectBlockCuts l) previous =
      columnRunHeads (l.map some) none := by
  cases l with
  | nil => rfl
  | cons a rest => simp [perfectBlockCuts, columnRunHeadsWithCuts, columnRunHeads, plainBlock_heads]




omit [DecidableEq α] in
theorem perfectBlockCuts_values (l : List α) :
    (perfectBlockCuts l).map Prod.fst = l.map some := by
  cases l <;> simp [perfectBlockCuts, List.map_map, Function.comp_def]

omit [DecidableEq α] in
theorem columnChunkCuts_values (chunks : List (List α ⊕ α)) :
    (columnChunkCuts chunks).map Prod.fst =
      (columnChunkEntries chunks).map (fun a => if a.2 then some a.1 else none) := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk <;>
        simp [columnChunkCuts, columnChunkEntries, Sum.elim, perfectBlockCuts_values,
          List.map_map, Function.comp_def] at ih ⊢ <;> exact ih

/-- Compression of the assembled column is exactly the concatenation of
its independently compressed perfect blocks. -/
theorem columnChunkCuts_heads (chunks : List (List α ⊕ α)) (previous : Option α) :
    columnRunHeadsWithCuts (columnChunkCuts chunks) previous = columnChunkRuns chunks := by
  induction chunks generalizing previous with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk with
      | inl block =>
          change columnRunHeadsWithCuts (perfectBlockCuts block ++ columnChunkCuts rest) previous =
            columnRunHeads (block.map some) none ++ columnChunkRuns rest
          rw [columnRunHeadsWithCuts_append, perfectBlockCuts_heads, ih]
      | inr a =>
          simpa [columnChunkCuts, columnRunHeadsWithCuts, columnChunkRuns] using ih none


theorem columnChunkPieces_flatten (omitted : α → Bool) (chunks : List (List α ⊕ α)) :
    (columnChunkPieces omitted chunks).flatMap (Sum.elim id List.singleton) =
      columnRunHeadsWithCuts (columnChunkCuts chunks) none := by
  rw [columnChunkCuts_heads]
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk <;>
        simp [columnChunkPieces, columnChunkRuns, Sum.elim, List.flatMap_append,
          partitionColumnRuns_flatten] at ih ⊢ <;> exact ih

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]

/-- Interval-shaped label occurrences imply the concrete omitted-run budget. -/
theorem block_omitted_piece_budget (l : List α) (omitted : Finset α)
    (hinterval : ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) :
    omittedPieceCount (partitionColumnRuns (fun a => decide (a ∈ omitted))
      (columnRunHeads (l.map some) none)) ≤ omitted.card := by
  let runs := columnRunHeads (l.map some) none
  have hn : (runs.filter (fun a => decide (a ∈ omitted))).Nodup :=
    (columnRunHeads_nodup l hinterval).filter _
  change ((partitionColumnRuns _ runs).filterMap _).length ≤ _
  rw [partitionColumnRuns_omitted, ← List.toFinset_card_of_nodup hn]
  apply card_le_card
  intro a ha
  exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp ha)).2

theorem block_regular_piece_budget (l : List α) (omitted : Finset α)
    (hinterval : ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) :
    regularPieceCount (partitionColumnRuns (fun a => decide (a ∈ omitted))
      (columnRunHeads (l.map some) none)) ≤ omitted.card + 1 := by
  have ho := block_omitted_piece_budget l omitted hinterval
  have hr := partitionColumnRuns_regular_count (fun a => decide (a ∈ omitted))
    (columnRunHeads (l.map some) none)
  have he := congrArg List.length (partitionColumnRuns_omitted
    (fun a => decide (a ∈ omitted)) (columnRunHeads (l.map some) none))
  change omittedPieceCount _ = _ at he
  omega


/-- Across actual perfect blocks, each omitted class is charged only once
per block, and every regular segment is charged to an omitted run or a block start. -/
theorem columnChunk_piece_budgets (chunks : List (List α ⊕ α)) (omitted : Finset α)
    (hinterval : ∀ l, Sum.inl l ∈ chunks → ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) :
    omittedPieceCount (columnChunkPieces (fun a => decide (a ∈ omitted)) chunks) ≤
        omitted.card * perfectChunkCount chunks ∧
    regularPieceCount (columnChunkPieces (fun a => decide (a ∈ omitted)) chunks) ≤
        (omitted.card + 1) * perfectChunkCount chunks := by
  induction chunks with
  | nil => simp [columnChunkPieces, perfectChunkCount, omittedPieceCount, regularPieceCount]
  | cons chunk rest ih =>
      have hir := ih (fun l hl => hinterval l (List.mem_cons_of_mem _ hl))
      cases chunk with
      | inl l =>
          have ho := block_omitted_piece_budget l omitted (hinterval l (List.mem_cons_self))
          have hr := block_regular_piece_budget l omitted (hinterval l (List.mem_cons_self))
          simp only [columnChunkPieces, List.flatMap_cons, Sum.elim_inl,
            omittedPieceCount_append, regularPieceCount_append]
          change _ ≤ omitted.card * (perfectChunkCount rest + 1) ∧
            _ ≤ (omitted.card + 1) * (perfectChunkCount rest + 1)
          constructor
          · change omittedPieceCount (partitionColumnRuns _ _) +
              omittedPieceCount (columnChunkPieces _ rest) ≤ _
            calc
              _ ≤ omitted.card + omitted.card * perfectChunkCount rest := Nat.add_le_add ho hir.1
              _ = _ := by ring
          · change regularPieceCount (partitionColumnRuns _ _) +
              regularPieceCount (columnChunkPieces _ rest) ≤ _
            calc
              _ ≤ (omitted.card + 1) + (omitted.card + 1) * perfectChunkCount rest :=
                Nat.add_le_add hr hir.2
              _ = _ := by ring
      | inr a =>
          simpa [columnChunkPieces, perfectChunkCount, List.filterMap_cons, Sum.elim] using hir

/-- The full merge mask fits in the original column length. -/
theorem columnChunkPieces_length_le (omitted : α → Bool) (chunks : List (List α ⊕ α)) :
    (columnChunkPieces omitted chunks).length ≤ (columnChunkEntries chunks).length := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk with
      | inl l =>
          have hl := (partitionColumnRuns_length_le omitted (columnRunHeads (l.map some) none)).trans
            (columnRunHeads_length_le (l.map some) none)
          simp only [List.length_map] at hl
          simpa only [columnChunkPieces, columnChunkEntries, List.flatMap_cons, Sum.elim_inl,
            List.length_append, List.length_map] using Nat.add_le_add hl ih
      | inr a =>
          simpa [columnChunkPieces, columnChunkEntries] using ih.trans (Nat.le_succ _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}


lemma shortBlockLengths_sum (n s : ℕ) : (shortBlockLengths n s).sum = n := by
  simpa [shortBlockLengths, Nat.mul_comm] using Nat.div_add_mod n s


@[simp] theorem shortBlocks_flatten (s : ℕ) (l : List α) : (shortBlocks s l).flatten = l := by
  exact List.flatten_splitLengths l _ (by rw [shortBlockLengths_sum])

@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]

theorem shortBlocks_size (s : ℕ) (hs : 0 < s) (l : List α) :
    ∀ block ∈ shortBlocks s l, block.length ≤ s := by
  apply List.length_mem_splitLengths
  intro n hn
  simp only [shortBlockLengths, List.mem_append, List.mem_replicate, List.mem_singleton] at hn
  rcases hn with ⟨_, rfl⟩ | rfl
  · exact le_rfl
  · exact (Nat.mod_lt _ hs).le

theorem shortBlocks_infix (s : ℕ) (l block : List α) (hb : block ∈ shortBlocks s l) :
    block.IsInfix l := by
  have h := List.infix_of_mem_flatten hb
  rwa [shortBlocks_flatten] at h


lemma columnChunkEntries_map_inl (blocks : List (List α)) :
    columnChunkEntries (blocks.map Sum.inl) = blocks.flatten.map (fun a => (a, true)) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      simpa [columnChunkEntries, Sum.elim, List.map_append] using
        congrArg (List.append (block.map (fun a => (a, true)))) ih

lemma columnChunkEntries_append (a b : List (List α ⊕ α)) :
    columnChunkEntries (a ++ b) = columnChunkEntries a ++ columnChunkEntries b := by
  simp [columnChunkEntries, List.flatMap_append]

/-- Subdivision preserves every position, including its perfect/imperfect status. -/
theorem subdivideColumnChunks_entries (s : ℕ) (chunks : List (List α ⊕ α)) :
    columnChunkEntries (subdivideColumnChunks s chunks) = columnChunkEntries chunks := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk with
      | inl l =>
          change columnChunkEntries ((shortBlocks s l).map Sum.inl ++ subdivideColumnChunks s rest) =
            l.map (fun a => (a, true)) ++ columnChunkEntries rest
          rw [columnChunkEntries_append, columnChunkEntries_map_inl, shortBlocks_flatten, ih]
      | inr a =>
          simpa [subdivideColumnChunks, columnChunkEntries] using
            congrArg (List.cons (a, false)) ih


lemma perfectChunkCount_append (a b : List (List α ⊕ α)) :
    perfectChunkCount (a ++ b) = perfectChunkCount a + perfectChunkCount b := by
  simp [perfectChunkCount, List.filterMap_append]

lemma perfectChunkCount_map_inl (blocks : List (List α)) :
    perfectChunkCount (blocks.map Sum.inl) = blocks.length := by
  simp [perfectChunkCount, List.filterMap_map, Function.comp_def, Sum.elim]

/-- The number of short perfect blocks is at most the total perfect length
 divided by the block size, plus the number of original perfect intervals. -/
theorem subdivideColumnChunks_count (s : ℕ) (chunks : List (List α ⊕ α)) :
    perfectChunkCount (subdivideColumnChunks s chunks) ≤
      perfectChunkLength chunks / s + perfectChunkCount chunks := by
  induction chunks with
  | nil => simp [subdivideColumnChunks, perfectChunkCount, perfectChunkLength]
  | cons chunk rest ih =>
      cases chunk with
      | inl l =>
          have hd := Nat.div_add_div_le_add_div (x := l.length) (y := perfectChunkLength rest) (z := s)
          change perfectChunkCount ((shortBlocks s l).map Sum.inl ++ subdivideColumnChunks s rest) ≤
            (l.length + perfectChunkLength rest) / s + (perfectChunkCount rest + 1)
          rw [perfectChunkCount_append, perfectChunkCount_map_inl, shortBlocks_length]
          omega
      | inr a =>
          simpa [subdivideColumnChunks, perfectChunkCount, perfectChunkLength, Sum.elim,
            List.filterMap_cons] using ih

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PerfectBlockPartition
namespace OAI

/-! Construct short perfect blocks from the actual position-status list. -/

namespace TwoPointCorrelations

variable {α β : Type*}


/-- The initial cut preserves every label and its original perfect status. -/
theorem initialColumnChunks_entries (entries : List (α × Bool)) :
    columnChunkEntries (initialColumnChunks entries) = entries := by
  let raw := partitionColumnRuns (fun a : α × Bool => !a.2) entries
  have hf := partitionColumnRuns_flatten (fun a : α × Bool => !a.2) entries
  change columnChunkEntries (raw.map (Sum.map (List.map Prod.fst) Prod.fst)) = entries
  apply Eq.trans _ hf
  simp only [columnChunkEntries, List.flatMap_map]
  apply List.flatMap_congr
  intro piece hp
  cases piece with
  | inl segment =>
      have hreg := (partitionColumnRuns_regular_entries (fun a : α × Bool => !a.2)
        entries segment hp).2
      simp only [Function.comp_def, Sum.map_inl, Sum.elim_inl, List.map_map, id_eq]
      calc
        _ = segment.map id := by
          apply List.map_congr_left
          intro a ha
          have hb := hreg a ha
          cases a with
          | mk a b => cases b <;> simp_all
        _ = segment := List.map_id _
  | inr a =>
      have hom : a ∈ raw.filterMap (Sum.elim (fun _ => none) some) :=
        List.mem_filterMap.mpr ⟨.inr a, hp, rfl⟩
      rw [show raw.filterMap (Sum.elim (fun _ => none) some) =
        entries.filter (fun a => !a.2) from partitionColumnRuns_omitted _ _] at hom
      have hb := (List.mem_filter.mp hom).2
      cases a with
      | mk a b => cases b <;> simp_all [Sum.map, Function.comp_def, List.singleton]

lemma perfectChunkCount_map (f : α → β) (chunks : List (List α ⊕ α)) :
    perfectChunkCount (chunks.map (Sum.map (List.map f) f)) = perfectChunkCount chunks := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih => cases chunk <;>
      simpa [perfectChunkCount, Sum.map, List.filterMap_cons, Sum.elim] using ih

lemma perfectChunkLength_le_entries (chunks : List (List α ⊕ α)) :
    perfectChunkLength chunks ≤ (columnChunkEntries chunks).length := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk with
      | inl l => simpa [perfectChunkLength, columnChunkEntries] using Nat.add_le_add_left ih l.length
      | inr a => simpa [perfectChunkLength, columnChunkEntries] using ih.trans (Nat.le_succ _)

/-- Each maximal perfect interval is charged to a preceding imperfect
position, except for a possible first interval. -/
theorem initialColumnChunks_count (entries : List (α × Bool)) :
    perfectChunkCount (initialColumnChunks entries) ≤
      (entries.filter (fun a => !a.2)).length + 1 := by
  unfold initialColumnChunks
  rw [perfectChunkCount_map]
  exact partitionColumnRuns_regular_count _ _


@[simp] theorem shortPerfectColumnChunks_entries (s : ℕ) (entries : List (α × Bool)) :
    columnChunkEntries (shortPerfectColumnChunks s entries) = entries := by
  rw [shortPerfectColumnChunks, subdivideColumnChunks_entries, initialColumnChunks_entries]

/-- This is the explicit one-half version of the manuscript's perfect-block
count. Applying it to both halves gives the stated absolute bound. -/
theorem shortPerfectColumnChunks_count (s : ℕ) (entries : List (α × Bool)) :
    perfectChunkCount (shortPerfectColumnChunks s entries) ≤
      entries.length / s + (entries.filter (fun a => !a.2)).length + 1 := by
  have h := subdivideColumnChunks_count s (initialColumnChunks entries)
  have hn := perfectChunkLength_le_entries (initialColumnChunks entries)
  rw [initialColumnChunks_entries] at hn
  have hd := Nat.div_le_div_right (c := s) hn
  have hc := initialColumnChunks_count entries
  exact h.trans (by omega)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnNameTransport
namespace OAI

/-! Transport the actual run decomposition to its canonical class names. -/

namespace TwoPointCorrelations

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem columnRunHeads_map (f : α → β) (l : List α)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b ↔ a = b) :
    (columnRunHeads (l.map some) none).map f =
      columnRunHeads ((l.map f).map some) none := by
  rw [columnRunHeads_eq_destutter, columnRunHeads_eq_destutter]
  exact List.map_destutter (fun a ha b hb => not_congr (hinj a ha b hb).symm)

theorem columnChunkRuns_map (f : α → β) (chunks : List (List α ⊕ α))
    (hinj : ∀ l, Sum.inl l ∈ chunks → ∀ a ∈ l, ∀ b ∈ l, f a = f b ↔ a = b) :
    (columnChunkRuns chunks).map f =
      columnChunkRuns (chunks.map (Sum.map (List.map f) f)) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      have hi := ih (fun l hl => hinj l (List.mem_cons_of_mem _ hl))
      cases chunk with
      | inl l =>
          simp only [List.map_cons, Sum.map_inl, columnChunkRuns, List.flatMap_cons,
            Sum.elim_inl, List.map_append]
          rw [columnRunHeads_map f l (hinj l List.mem_cons_self)]
          exact congrArg (fun tail => columnRunHeads ((l.map f).map some) none ++ tail) hi
      | inr a => simpa only [columnChunkRuns, List.flatMap_cons, Sum.elim_inr, List.map_nil,
          List.nil_append, List.map_cons, Sum.map_inr] using hi

omit [DecidableEq α] [DecidableEq β] in
theorem mapped_pieces_flatten (f : α → β) (pieces : List (List α ⊕ α)) :
    (pieces.map (Sum.map (List.map f) f)).flatMap (Sum.elim id List.singleton) =
      (pieces.flatMap (Sum.elim id List.singleton)).map f := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece <;> simp only [List.map_cons, Sum.map_inl, Sum.map_inr,
        List.flatMap_cons, Sum.elim_inl, Sum.elim_inr, List.map_append,
        id_eq] <;> rw [ih]
      all_goals simp only [List.singleton, List.map_cons, List.map_nil]

/-- Canonical renaming preserves the exact merge list when it preserves
the equality relation on each actual block. -/
theorem mapped_column_pieces_heads (f : α → β) (omitted : α → Bool)
    (chunks : List (List α ⊕ α))
    (hinj : ∀ l, Sum.inl l ∈ chunks → ∀ a ∈ l, ∀ b ∈ l, f a = f b ↔ a = b) :
    ((columnChunkPieces omitted chunks).map (Sum.map (List.map f) f)).flatMap
        (Sum.elim id List.singleton) =
      columnRunHeadsWithCuts (columnChunkCuts (chunks.map (Sum.map (List.map f) f))) none := by
  rw [mapped_pieces_flatten, columnChunkPieces_flatten, columnChunkCuts_heads,
    columnChunkCuts_heads, columnChunkRuns_map f chunks hinj]

omit [DecidableEq α] [DecidableEq β] in
theorem mapped_pieces_regular (f : α → β) (pieces : List (List α ⊕ α)) :
    (pieces.map (Sum.map (List.map f) f)).filterMap (Sum.elim some (fun _ => none)) =
      (pieces.filterMap (Sum.elim some (fun _ => none))).map (List.map f) := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece <;> simp only [List.map_cons, Sum.map_inl, Sum.map_inr,
        List.filterMap_cons, Sum.elim_inl, Sum.elim_inr] <;> rw [ih]

omit [DecidableEq α] [DecidableEq β] in
theorem mapped_pieces_omitted (f : α → β) (pieces : List (List α ⊕ α)) :
    (pieces.map (Sum.map (List.map f) f)).filterMap (Sum.elim (fun _ => none) some) =
      (pieces.filterMap (Sum.elim (fun _ => none) some)).map f := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece <;> simp only [List.map_cons, Sum.map_inl, Sum.map_inr,
        List.filterMap_cons, Sum.elim_inl, Sum.elim_inr] <;> rw [ih]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnPieceMembership
namespace OAI

/-! Membership information retained by the actual perfect-block cut. -/

namespace TwoPointCorrelations

variable {α β : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem columnChunkEntries_map (f : α → β) (chunks : List (List α ⊕ α)) :
    columnChunkEntries (chunks.map (Sum.map (List.map f) f)) =
      (columnChunkEntries chunks).map (fun a => (f a.1, a.2)) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      cases chunk <;> simp only [List.map_cons, Sum.map_inl, Sum.map_inr,
        columnChunkEntries, List.flatMap_cons, Sum.elim_inl, Sum.elim_inr,
        List.map_append, List.map_map, Function.comp_def, List.map_nil] at ih ⊢ <;> rw [ih]

theorem columnRunHeads_mem_original (l : List α) (a : α)
    (ha : a ∈ columnRunHeads (l.map some) none) : a ∈ l := by
  rw [columnRunHeads_eq_destutter] at ha
  exact (List.destutter_sublist (R := (· ≠ ·)) l).subset ha

/-- A regular piece retains both its regular status and a genuinely
perfect occurrence in the original column. -/
theorem columnChunkPieces_regular_membership (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (segment : List α)
    (hs : Sum.inl segment ∈ columnChunkPieces omitted chunks) :
    segment ≠ [] ∧ ∀ a ∈ segment, omitted a = false ∧ (a, true) ∈ columnChunkEntries chunks := by
  obtain ⟨chunk, hc, hs⟩ := List.mem_flatMap.mp hs
  cases chunk with
  | inr a => simp at hs
  | inl block =>
      have hr := partitionColumnRuns_regular_entries omitted
        (columnRunHeads (block.map some) none) segment hs
      refine ⟨hr.1, ?_⟩
      intro a ha
      have hm := (partitionColumnRuns_regular_infix omitted
        (columnRunHeads (block.map some) none) segment hs).subset ha
      have hb := columnRunHeads_mem_original block a hm
      exact ⟨hr.2 a ha, List.mem_flatMap.mpr ⟨.inl block, hc, List.mem_map.mpr ⟨a, hb, rfl⟩⟩⟩

/-- Omitted runs also come from perfect positions; their separate names
therefore fit within the original occurrence-index bound. -/
theorem columnChunkPieces_omitted_membership (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (a : α)
    (ha : Sum.inr a ∈ columnChunkPieces omitted chunks) :
    omitted a = true ∧ (a, true) ∈ columnChunkEntries chunks := by
  obtain ⟨chunk, hc, ha⟩ := List.mem_flatMap.mp ha
  cases chunk with
  | inr z => simp at ha
  | inl block =>
      have hm : a ∈ (partitionColumnRuns omitted (columnRunHeads (block.map some) none)).filterMap
          (Sum.elim (fun _ => none) some) := List.mem_filterMap.mpr ⟨.inr a, ha, rfl⟩
      rw [partitionColumnRuns_omitted] at hm
      obtain ⟨hr, ho⟩ := List.mem_filter.mp hm
      have hb := columnRunHeads_mem_original block a hr
      exact ⟨ho, List.mem_flatMap.mpr ⟨.inl block, hc, List.mem_map.mpr ⟨a, hb, rfl⟩⟩⟩

omit [DecidableEq α] in
/-- A bounded list of omitted canonical names has an equally long list
of decoder indices, so no extra naming cost is introduced. -/
theorem omitted_names_lift {N : ℕ} (names : List CanonicalColumnLabel)
    (h : ∀ a ∈ names, ∃ j : Fin N, a = .omitted j.val) :
    ∃ indices : List (Fin N), indices.length = names.length ∧
      indices.map (fun j => CanonicalColumnLabel.omitted j.val) = names := by
  induction names with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a names ih =>
      obtain ⟨j, hj⟩ := h a List.mem_cons_self
      obtain ⟨indices, hl, he⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      exact ⟨j :: indices, by simp only [List.length_cons, hl], by rw [List.map_cons, he, ← hj]⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.IndexedRuns
namespace OAI

/-! Indexed run starts retain the constant intervals needed for quotient paths. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]


/-- The scan retains the complete constant interval between consecutive
run starts, not just the unequal labels. -/
theorem scanRunTransitions_chain (label : ℕ → α) (a n len : ℕ) (i : α)
    (han : a < n) (hcurrent : label a = i)
    (hconst : ∀ t ∈ Ico a n, label t = i) :
    ((a, i) :: scanRunTransitions label n len i).IsChain (IndexedRunStep label) := by
  induction len generalizing a n i with
  | zero => exact .singleton _
  | succ len ih =>
      by_cases heq : label n = i
      · rw [scanRunTransitions, if_pos heq]
        apply ih a (n + 1) i (by omega) hcurrent
        intro t ht
        rcases mem_Ico.mp ht with ⟨hat, htn⟩
        by_cases htn' : t < n
        · exact hconst t (mem_Ico.mpr ⟨hat, htn'⟩)
        · have he : t = n := by omega
          simpa only [he] using heq
      · rw [scanRunTransitions, if_neg heq]
        apply List.IsChain.cons_cons
        · exact ⟨han, hcurrent, rfl, Ne.symm heq, hconst⟩
        · apply ih n (n + 1) (label n) (by omega) rfl
          intro t ht
          have he : t = n := by have := mem_Ico.mp ht; omega
          simp only [he]

/-- Labels in a scan agree with the actual numerical positions they record. -/
theorem scanRunTransitions_mem (label : ℕ → α) (n len : ℕ) (previous : α)
    (p : ℕ × α) (hp : p ∈ scanRunTransitions label n len previous) :
    n ≤ p.1 ∧ p.1 < n + len ∧ label p.1 = p.2 := by
  induction len generalizing n previous with
  | zero => simp [scanRunTransitions] at hp
  | succ len ih =>
      by_cases heq : label n = previous
      · rw [scanRunTransitions, if_pos heq] at hp
        obtain ⟨hl, hu, he⟩ := ih (n + 1) previous hp
        exact ⟨by omega, by omega, he⟩
      · rw [scanRunTransitions, if_neg heq, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨le_rfl, by omega, rfl⟩
        · obtain ⟨hl, hu, he⟩ := ih (n + 1) (label n) hp
          exact ⟨by omega, by omega, he⟩


theorem indexedBlockRuns_chain (label : ℕ → α) (start len : ℕ) :
    (indexedBlockRuns label start len).IsChain (IndexedRunStep label) := by
  cases len with
  | zero => exact .nil
  | succ len =>
      apply scanRunTransitions_chain label start (start + 1) len (label start) (by omega) rfl
      intro t ht
      have he : t = start := by have := mem_Ico.mp ht; omega
      simp only [he]

theorem indexedBlockRuns_mem (label : ℕ → α) (start len : ℕ) (p : ℕ × α)
    (hp : p ∈ indexedBlockRuns label start len) :
    start ≤ p.1 ∧ p.1 < start + len ∧ label p.1 = p.2 := by
  cases len with
  | zero => simp [indexedBlockRuns] at hp
  | succ len =>
      simp only [indexedBlockRuns, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨le_rfl, by omega, rfl⟩
      · obtain ⟨hl, hu, he⟩ := scanRunTransitions_mem label (start + 1) len (label start) p hp
        exact ⟨by omega, by omega, he⟩


omit [DecidableEq α] in
lemma blockLabelList_succ (label : ℕ → α) (start len : ℕ) :
    blockLabelList label start (len + 1) = label start :: blockLabelList label (start + 1) len := by
  simp only [blockLabelList, List.range_succ_eq_map, List.map_cons, Nat.add_zero,
    List.map_map, Function.comp_def]
  congr 2
  funext j
  congr 1
  omega

lemma scanRunTransitions_labels (label : ℕ → α) (n len : ℕ) (previous : α) :
    (scanRunTransitions label n len previous).map Prod.snd =
      columnRunHeads ((blockLabelList label n len).map some) (some previous) := by
  induction len generalizing n previous with
  | zero => rfl
  | succ len ih =>
      rw [blockLabelList_succ]
      by_cases heq : label n = previous
      · simp [scanRunTransitions, columnRunHeads, heq, ih]
      · have hne : previous ≠ label n := Ne.symm heq
        simp [scanRunTransitions, columnRunHeads, heq, hne, ih]

/-- Forgetting positions recovers precisely the run list used by the decoder. -/
theorem indexedBlockRuns_labels (label : ℕ → α) (start len : ℕ) :
    (indexedBlockRuns label start len).map Prod.snd =
      columnRunHeads ((blockLabelList label start len).map some) none := by
  cases len with
  | zero => rfl
  | succ len =>
      simp only [indexedBlockRuns, List.map_cons, scanRunTransitions_labels,
        blockLabelList_succ, List.map_cons, columnRunHeads]
      simp

/-- Thus cutting indexed runs into regular segments yields exactly the
same label pieces as cutting the decoder's compressed block. -/
theorem indexedBlockRuns_partition (label : ℕ → α) (start len : ℕ) (omitted : α → Bool) :
    (partitionColumnRuns (fun p => omitted p.2) (indexedBlockRuns label start len)).map
        (Sum.map (List.map Prod.snd) Prod.snd) =
      partitionColumnRuns omitted (columnRunHeads ((blockLabelList label start len).map some) none) := by
  rw [← partitionColumnRuns_map, indexedBlockRuns_labels]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PerfectBlockPositions
namespace OAI

/-! The constructed perfect blocks are actual contiguous intervals of positions. -/

namespace TwoPointCorrelations

variable {α : Type*}

theorem subdivideColumnChunks_regular_origin (s : ℕ) (chunks : List (List α ⊕ α))
    (block : List α) (hb : Sum.inl block ∈ subdivideColumnChunks s chunks) :
    ∃ large, Sum.inl large ∈ chunks ∧ block ∈ shortBlocks s large := by
  obtain ⟨piece, hp, hb⟩ := List.mem_flatMap.mp hb
  cases piece with
  | inl large =>
      simp only [Sum.elim_inl, List.mem_map, Sum.inl.injEq] at hb
      obtain ⟨l, hl, rfl⟩ := hb
      exact ⟨large, hp, hl⟩
  | inr a => simp at hb

theorem initialColumnChunks_regular_origin (entries : List (α × Bool))
    (block : List α) (hb : Sum.inl block ∈ initialColumnChunks entries) :
    ∃ raw, Sum.inl raw ∈ partitionColumnRuns (fun a : α × Bool => !a.2) entries ∧
      block = raw.map Prod.fst := by
  obtain ⟨piece, hp, he⟩ := List.mem_map.mp hb
  cases piece with
  | inl raw =>
      simp only [Sum.map_inl, Sum.inl.injEq] at he
      exact ⟨raw, hp, he.symm⟩
  | inr a => simp at he

/-- Every constructed block is a contiguous part of the original column,
and all its positions have their original perfect status. -/
theorem shortPerfectColumnChunks_regular_positions (s : ℕ) (entries : List (α × Bool))
    (block : List α) (hb : Sum.inl block ∈ shortPerfectColumnChunks s entries) :
    block.IsInfix (entries.map Prod.fst) ∧ ∀ a ∈ block, (a, true) ∈ entries := by
  obtain ⟨large, hl, hsub⟩ := subdivideColumnChunks_regular_origin s
    (initialColumnChunks entries) block hb
  obtain ⟨raw, hr, rfl⟩ := initialColumnChunks_regular_origin entries large hl
  have hi := partitionColumnRuns_regular_infix (fun a : α × Bool => !a.2) entries raw hr
  have hs := shortBlocks_infix s (raw.map Prod.fst) block hsub
  refine ⟨hs.trans (hi.map Prod.fst), ?_⟩
  intro a ha
  obtain ⟨p, hp, he⟩ := List.mem_map.mp (hs.subset ha)
  have hpreg := (partitionColumnRuns_regular_entries (fun a : α × Bool => !a.2) entries raw hr).2 p hp
  have hmem := hi.subset hp
  rcases p with ⟨b, perfect⟩
  cases perfect <;> simp_all

/-- A prefix of the position-indexed label list is the same label list
with the shortened length. -/
theorem blockLabelList_take (label : ℕ → α) (start total len : ℕ) (h : len ≤ total) :
    (blockLabelList label start total).take len = blockLabelList label start len := by
  induction len generalizing start total with
  | zero => simp [blockLabelList]
  | succ len ih =>
      cases total with
      | zero => omega
      | succ total =>
          rw [blockLabelList_succ, blockLabelList_succ, List.take_succ_cons, ih]
          omega

theorem blockLabelList_drop_take (label : ℕ → α) (start total a len : ℕ)
    (h : a + len ≤ total) :
    ((blockLabelList label start total).drop a).take len = blockLabelList label (start + a) len := by
  induction a generalizing start total with
  | zero => simpa using blockLabelList_take label start total len (by simpa using h)
  | succ a ih =>
      cases total with
      | zero => omega
      | succ total =>
          rw [blockLabelList_succ, List.drop_succ_cons, ih (start + 1) total (by omega)]
          congr 1
          omega

/-- Every contiguous part of a position-indexed list has an actual bounded
starting index, so no extra run-position data need be postulated. -/
theorem infix_blockLabelList_positions (label : ℕ → α) (start total : ℕ)
    (block : List α) (hb : block.IsInfix (blockLabelList label start total)) :
    ∃ a, a + block.length ≤ total ∧ block = blockLabelList label (start + a) block.length := by
  obtain ⟨before, after, he⟩ := hb
  have hlen : before.length + block.length ≤ total := by
    have ht := congrArg List.length he
    simp only [List.length_append, blockLabelList, List.length_map, List.length_range] at ht
    omega
  refine ⟨before.length, hlen, ?_⟩
  rw [← blockLabelList_drop_take label start total before.length block.length hlen, ← he]
  simp

/-- Each short block has the promised maximum length. -/
theorem shortPerfectColumnChunks_regular_size (s : ℕ) (hs : 0 < s)
    (entries : List (α × Bool)) (block : List α)
    (hb : Sum.inl block ∈ shortPerfectColumnChunks s entries) : block.length ≤ s := by
  obtain ⟨large, _, hsub⟩ := subdivideColumnChunks_regular_origin s
    (initialColumnChunks entries) block hb
  exact shortBlocks_size s hs large block hsub

/-- On the actual consecutive position list, every generated block has a
bounded starting index and contains only perfect positions. -/
theorem shortPerfectColumnChunks_position_intervals (N s : ℕ) (perfect : ℕ → Bool)
    (block : List ℕ)
    (hb : Sum.inl block ∈ shortPerfectColumnChunks s
      ((List.range N).map (fun i => (i, perfect i)))) :
    ∃ start, start + block.length ≤ N ∧
      block = (List.range block.length).map (fun i => start + i) ∧
      ∀ i ∈ block, perfect i = true := by
  obtain ⟨hinfix, hperfect⟩ := shortPerfectColumnChunks_regular_positions s _ block hb
  have hi : block.IsInfix (blockLabelList id 0 N) := by
    simpa [blockLabelList, List.map_map, Function.comp_def] using hinfix
  obtain ⟨start, hbound, hblock⟩ := infix_blockLabelList_positions id 0 N block hi
  refine ⟨start, hbound, ?_, ?_⟩
  · simpa [blockLabelList] using hblock
  · intro i hi
    obtain ⟨j, _, heq⟩ := List.mem_map.mp (hperfect i hi)
    have hji : j = i := congrArg Prod.fst heq
    simpa only [hji] using congrArg Prod.snd heq

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PerfectIntervalFamily
namespace OAI

/-! Choose numerical intervals for the constructed perfect blocks, preserving all budgets. -/

namespace TwoPointCorrelations


private theorem choose_interval_family (N : ℕ) (perfect : ℕ → Bool)
    (blocks : List (List ℕ))
    (hblocks : ∀ block ∈ blocks, ∃ start, start + block.length ≤ N ∧
      block = intervalPositions (start, block.length) ∧ ∀ i ∈ block, perfect i = true) :
    ∃ intervals : List (ℕ × ℕ), intervals.map intervalPositions = blocks ∧
      ∀ b ∈ intervals, b.1 + b.2 ≤ N ∧ ∀ i ∈ intervalPositions b, perfect i = true := by
  induction blocks with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons block blocks ih =>
      obtain ⟨start, hbound, heq, hp⟩ := hblocks block List.mem_cons_self
      obtain ⟨intervals, hi, hv⟩ := ih (fun b hb => hblocks b (List.mem_cons_of_mem _ hb))
      refine ⟨(start, block.length) :: intervals, ?_, ?_⟩
      · simpa only [List.map_cons, hi] using congrArg (fun tail => tail :: blocks) heq.symm
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨hbound, by simpa only [← heq] using hp⟩
        · exact hv b hb

variable {α : Type*}

theorem perfectChunkLength_eq_sum (chunks : List (List α ⊕ α)) :
    perfectChunkLength chunks =
      ((chunks.filterMap (Sum.elim some (fun _ => none))).map List.length).sum := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      cases chunk with
      | inl block =>
          simpa [perfectChunkLength, List.filterMap_cons, Sum.elim] using
            congrArg (fun n => block.length + n) ih
      | inr a =>
          simpa [perfectChunkLength, List.filterMap_cons, Sum.elim] using ih

/-- The actual short-block partition admits numerical interval parameters.
Their total length is at most the original length; every selected position
retains its original perfect flag. Empty terminal blocks cost zero. -/
theorem shortPerfectColumnChunks_interval_family (N s : ℕ) (perfect : ℕ → Bool) :
    ∃ intervals : List (ℕ × ℕ),
      intervals.map intervalPositions =
        ((shortPerfectColumnChunks s ((List.range N).map (fun i => (i, perfect i)))).filterMap
          (Sum.elim some (fun _ => none))) ∧
      intervals.length = perfectChunkCount
        (shortPerfectColumnChunks s ((List.range N).map (fun i => (i, perfect i)))) ∧
      (intervals.map Prod.snd).sum ≤ N ∧
      ∀ b ∈ intervals, b.1 + b.2 ≤ N ∧ ∀ i ∈ intervalPositions b, perfect i = true := by
  let chunks := shortPerfectColumnChunks s ((List.range N).map (fun i => (i, perfect i)))
  obtain ⟨intervals, he, hv⟩ := choose_interval_family N perfect
    (chunks.filterMap (Sum.elim some (fun _ => none))) (by
      intro block hb
      obtain ⟨piece, hp, heq⟩ := List.mem_filterMap.mp hb
      cases piece with
      | inl b =>
          cases heq
          exact shortPerfectColumnChunks_position_intervals N s perfect block hp
      | inr a => simp at heq)
  refine ⟨intervals, he, ?_, ?_, hv⟩
  · have h := congrArg List.length he
    simpa only [List.length_map, perfectChunkCount] using h
  · have hlen : (intervals.map Prod.snd).sum = perfectChunkLength chunks := by
      rw [perfectChunkLength_eq_sum, ← he, List.map_map]
      simp only [intervalPositions, List.length_map, List.length_range, Function.comp_def]
    rw [hlen]
    have h := perfectChunkLength_le_entries chunks
    rw [show columnChunkEntries chunks = (List.range N).map (fun i => (i, perfect i)) from
      shortPerfectColumnChunks_entries s _] at h
    simpa only [List.length_map, List.length_range] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortColumnBlocks
namespace OAI

/-! The actual short perfect blocks of a finite column, with all positions and budgets. -/

namespace TwoPointCorrelations

variable {α : Type*} {n : ℕ}



theorem columnNatLabel_fin (label : Fin n → α) (hn : 0 < n) (i : Fin n) :
    columnNatLabel label hn i.val = label i := by
  simp only [columnNatLabel, dif_pos i.isLt, Fin.eta]

theorem columnNatPerfect_fin (perfect : Finset (Fin n)) (i : Fin n) :
    columnNatPerfect perfect i.val = decide (i ∈ perfect) := by
  simp [columnNatPerfect, i.isLt]

theorem range_map_eq_ofFn {β : Type*} (f : ℕ → β) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  simpa using (List.ofFn_getElem_eq_map (List.range n) f).symm


theorem shortColumnChunks_entries (label : Fin n → α) (hn : 0 < n)
    (perfect : Finset (Fin n)) (s : ℕ) :
    columnChunkEntries (shortColumnChunks label hn perfect s) =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)) := by
  rw [shortColumnChunks, columnChunkEntries_map, shortPerfectColumnChunks_entries]
  simp only [Function.comp_def, range_map_eq_ofFn, columnNatLabel_fin,
    columnNatPerfect_fin, columnPositionEntries, List.map_ofFn]

/-- The short blocks used by the decoder are actual intervals, all of
length at most `s`. Their count and total length satisfy the original
position budgets, before any quotient geometry is used. -/
theorem shortColumnChunks_blocks (label : Fin n → α) (hn : 0 < n)
    (perfect : Finset (Fin n)) (s : ℕ) (hs : 0 < s) :
    ∃ blocks : List (ℕ × ℕ),
      (shortColumnChunks label hn perfect s).filterMap (Sum.elim some (fun _ => none)) =
        blocks.map (fun b => blockLabelList (columnNatLabel label hn) b.1 b.2) ∧
      (blocks.map Prod.snd).sum ≤ n ∧
      blocks.length ≤ n / s + ((columnPositionEntries perfect).filter (fun p => !p.2)).length + 1 ∧
      ∀ b ∈ blocks, b.1 + b.2 ≤ n ∧ b.2 ≤ s ∧
        ∀ t ∈ intervalPositions b, columnNatPerfect perfect t = true := by
  let entries := (List.range n).map (fun t => (t, columnNatPerfect perfect t))
  let chunks := shortPerfectColumnChunks s entries
  obtain ⟨blocks, hblocks, hcount, hsum, hvalid⟩ :=
    shortPerfectColumnChunks_interval_family n s (columnNatPerfect perfect)
  refine ⟨blocks, ?_, hsum, ?_, ?_⟩
  · change (chunks.map (Sum.map (List.map (columnNatLabel label hn)) (columnNatLabel label hn))).filterMap _ = _
    rw [mapped_pieces_regular, ← hblocks, List.map_map]
    simp only [intervalPositions, blockLabelList, List.map_map, Function.comp_def]
  · have hc := shortPerfectColumnChunks_count s entries
    rw [← hcount] at hc
    have hflags : (entries.filter (fun p => !p.2)).length =
        ((columnPositionEntries perfect).filter (fun p => !p.2)).length := by
      have he : entries = (columnPositionEntries perfect).map (fun p => (p.1.val, p.2)) := by
        simp only [entries, range_map_eq_ofFn, columnNatPerfect_fin, columnPositionEntries, List.map_ofFn, Function.comp_def]
      rw [he, List.filter_map, List.length_map]
      rfl
    have he : entries.length = n := by simp only [entries, List.length_map, List.length_range]
    simpa only [he, hflags] using hc
  · intro b hb
    refine ⟨(hvalid b hb).1, ?_, (hvalid b hb).2⟩
    have hm : intervalPositions b ∈ chunks.filterMap (Sum.elim some (fun _ => none)) := by
      rw [← hblocks]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨piece, hp, he⟩ := List.mem_filterMap.mp hm
    have hi : Sum.inl (intervalPositions b) ∈ chunks := by
      cases piece with
      | inl block => cases he; exact hp
      | inr a => simp at he
    have hl := shortPerfectColumnChunks_regular_size s hs entries (intervalPositions b) hi
    simpa only [intervalPositions, List.length_map, List.length_range] using hl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordSegments
namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl

lemma wordDisplacement_take (h : ℕ) (w : List SignedStep) (n : ℕ) :
    wordDisplacement h (w.take n) = ∑ i ∈ range n, wordStepDisplacement h w i := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      cases w with
      | nil => simp
      | cons a w =>
          rw [List.take_succ_cons, wordDisplacement_cons, Finset.sum_range_succ']
          simp only [wordStepDisplacement_cons_zero, wordStepDisplacement_cons_succ, ih]
          ring


lemma wordSlice_length (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ w.length) :
    (wordSlice w a b).length = b - a := by
  simp only [wordSlice, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

lemma wordSlice_split (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) :
    w.take a ++ wordSlice w a b = w.take b := by
  have h := List.take_append_drop a (w.take b)
  simpa only [List.take_take, Nat.min_eq_left hab, List.drop_take, wordSlice] using h

lemma wordSlice_infix (w : List SignedStep) (a b : ℕ) : wordSlice w a b <:+: w := by
  refine ⟨w.take a, (w.drop a).drop (b - a), ?_⟩
  change (w.take a ++ (w.drop a).take (b - a)) ++ (w.drop a).drop (b - a) = w
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

lemma wordSlice_displacement (h : ℕ) (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) :
    wordDisplacement h (wordSlice w a b) = intervalDisplacement (wordStepDisplacement h w) a b := by
  have hs := congrArg (wordDisplacement h) (wordSlice_split w hab)
  rw [wordDisplacement_append, wordDisplacement_take, wordDisplacement_take] at hs
  rw [intervalDisplacement_eq_sub _ hab]
  omega

lemma wordSlice_drop (w : List SignedStep) {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b) :
    (wordSlice w a b).drop (c - a) = wordSlice w c b := by
  simp only [wordSlice, List.drop_take, List.drop_drop]
  rw [show b - a - (c - a) = b - c by omega,
    show a + (c - a) = c by omega]

lemma tuplePrimeAt_slice (w : List SignedStep) (a b p i : ℕ) (hi : i < b - a) :
    TuplePrimeAt (wordSlice w a b) p i ↔ TuplePrimeAt w p (a + i) := by
  unfold TuplePrimeAt wordSlice
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop]

lemma TuplePrimeAt.index_lt {w : List SignedStep} {p i : ℕ} (hp : TuplePrimeAt w p i) :
    i < w.length := by
  obtain ⟨_, a, ha, _⟩ := hp
  exact (List.getElem?_eq_some_iff.mp ha).1

/-- The purely local interval prohibition is exactly a forward-prohibited
list segment when eligibility and unequal consecutive tuples are retained. -/
lemma prohibitedInterval_forward_wordSlice (h s : ℕ) (supply : ℕ → ℕ → Prop)
    (w : List SignedStep) (hlen : w.length ≤ s)
    (hsupply : ∀ t ∈ w, supply t.tuple t.padding)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple)) {a b : ℕ}
    (hb : b ≤ w.length)
    (hpro : ProhibitedInterval (TuplePrimeAt w) (wordStepDisplacement h w) id a b) :
    ForwardProhibited h s supply (wordSlice w a b) := by
  rcases hpro with ⟨hlenab, hinterval, p, hfirst, hlast, c, hac, hcb, hdiv⟩
  have hab : a ≤ b := by omega
  have hlength := wordSlice_length w hab hb
  refine ⟨by omega, by omega, ?_, (hchain.drop a).take (b - a), ?_, p, ?_, ?_,
    c - a, by omega, by omega, ?_⟩
  · intro t ht
    exact hsupply t ((wordSlice_infix w a b).subset ht)
  · intro q i j k hij hjk hk hqi hqk
    have hi : i < b - a := by omega
    have hj : j < b - a := by omega
    have hk' : k < b - a := by omega
    apply (tuplePrimeAt_slice w a b q j hj).mpr
    apply hinterval q (a + i) (a + j) (a + k) (by omega) (by omega) (by omega) (by omega)
    · exact (tuplePrimeAt_slice w a b q i hi).mp hqi
    · exact (tuplePrimeAt_slice w a b q k hk').mp hqk
  · simpa only [Nat.add_zero] using (tuplePrimeAt_slice w a b p 0 (by omega)).mpr hfirst
  · intro hp
    have hp' := (tuplePrimeAt_slice w a b p ((wordSlice w a b).length - 1) (by omega)).mp hp
    have heq : a + ((wordSlice w a b).length - 1) = b - 1 := by omega
    exact hlast (heq ▸ hp')
  · rw [wordSlice_drop w hac.le (by omega), wordSlice_displacement h w (by omega)]
    exact hdiv

/-- The local prohibition hypothesis used by block geometry is discharged
from survival of the actual main vertices, via concrete witness descent. -/
theorem PositiveWord.avoids_prohibitedIntervals {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {x : ℤ} {w : List SignedStep} (hw : PositiveWord h x w)
    (hsurvive : ∀ y, WordVertex h x w y → ¬ProhibitedSite h s supply y)
    (hlen : w.length ≤ s) (hsupply : ∀ t ∈ w, supply t.tuple t.padding)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    ∀ a b, b ≤ w.length → ¬ProhibitedInterval (TuplePrimeAt w) (wordStepDisplacement h w) id a b := by
  intro a b hb hpro
  have hword := prohibitedInterval_forward_wordSlice h s supply w hlen hsupply hchain hb hpro
  exact hw.not_prohibited_orientedInfix hsurvive (Or.inl (wordSlice_infix w a b)) hword

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordBlockGeometry
namespace OAI

/-! Geometry of actual surviving positive words, including the prime-support checks. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma tuplePrimeAt_iff_getElem (w : List SignedStep) (p i : ℕ) (hi : i < w.length) :
    TuplePrimeAt w p i ↔ p.Prime ∧ p ∣ w[i].tuple := by
  simp [TuplePrimeAt, List.getElem?_eq_getElem hi]

lemma wordStepDisplacement_getElem (h : ℕ) (w : List SignedStep) (i : ℕ) (hi : i < w.length) :
    wordStepDisplacement h w i = w[i].displacement h := by
  simp [wordStepDisplacement, List.getElem?_eq_getElem hi]

lemma tuplePrime_dvd_step {h p i : ℕ} {w : List SignedStep} (hp : TuplePrimeAt w p i) :
    (p : ℤ) ∣ wordStepDisplacement h w i := by
  have hi := hp.index_lt
  have hpd := ((tuplePrimeAt_iff_getElem w p i hi).mp hp).2
  have hcast : (p : ℤ) ∣ (w[i].tuple : ℤ) := by exact_mod_cast hpd
  rw [wordStepDisplacement_getElem h w i hi]
  exact (hcast.mul_left (w[i].padding : ℤ)).trans (w[i].divisor_dvd_displacement h)

/-- Positivity supplies each tuple-prime divisibility at the exact prefix sum. -/
lemma PositiveWord.tuplePrime_departure {h p i : ℕ} {x : ℤ} {w : List SignedStep}
    (hw : PositiveWord h x w) (hp : TuplePrimeAt w p i) :
    (p : ℤ) ∣ x + wordDisplacement h (w.take i) := by
  induction w generalizing x i with
  | nil => simp [TuplePrimeAt] at hp
  | cons a w ih =>
      rcases hw with ⟨ha, hw⟩
      cases i with
      | zero =>
          have hp' := (tuplePrimeAt_iff_getElem (a :: w) p 0 (by simp)).mp hp
          have hcast : (p : ℤ) ∣ (a.tuple : ℤ) := by exact_mod_cast hp'.2
          simpa only [List.take_zero, wordDisplacement_nil, add_zero] using
            (hcast.mul_left (a.padding : ℤ)).trans ha
      | succ i =>
          have hp' : TuplePrimeAt w p i := by simpa [TuplePrimeAt] using hp
          simpa only [List.take_succ_cons, wordDisplacement_cons, add_assoc] using ih hw hp'

lemma PositiveWord.tuplePrime_departure_sum {h : ℕ} {x : ℤ} {w : List SignedStep}
    (hw : PositiveWord h x w) : ∀ p i, i < w.length → TuplePrimeAt w p i →
      (p : ℤ) ∣ x + ∑ a ∈ range i, wordStepDisplacement h w a := by
  intro p i _ hp
  rw [← wordDisplacement_take]
  exact hw.tuplePrime_departure hp

/-- Equal-size squarefree whole tuples cannot change by merely adding primes:
a changed tuple loses at least one prime from the preceding tuple. -/
lemma adjacent_tuple_prime_change (w : List SignedStep) (J : ℕ)
    (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    ∀ i, i + 1 < w.length → ∃ p, TuplePrimeAt w p i ∧ ¬TuplePrimeAt w p (i + 1) := by
  intro i hi
  have hi0 : i < w.length := by omega
  have ha := List.getElem_mem hi0
  have hb := List.getElem_mem hi
  have hneq : w[i].tuple ≠ w[i + 1].tuple := (List.isChain_iff_getElem.mp hchain) i hi
  have hsets : w[i].tuple.primeFactors ≠ w[i + 1].tuple.primeFactors := by
    intro heq
    apply hneq
    calc
      _ = ∏ p ∈ w[i].tuple.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hsq _ ha)).symm
      _ = ∏ p ∈ w[i + 1].tuple.primeFactors, p := by rw [heq]
      _ = _ := Nat.prod_primeFactors_of_squarefree (hsq _ hb)
  have hnot : ¬w[i].tuple.primeFactors ⊆ w[i + 1].tuple.primeFactors := by
    intro hsub
    apply hsets
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard _ ha, hcard _ hb])
  obtain ⟨p, hpa, hpb⟩ := Finset.not_subset.mp hnot
  have hp := Nat.mem_primeFactors.mp hpa
  refine ⟨p, (tuplePrimeAt_iff_getElem w p i hi0).mpr ⟨hp.1, hp.2.1⟩, ?_⟩
  intro hpi
  have hpbi := (tuplePrimeAt_iff_getElem w p (i + 1) hi).mp hpi
  exact hpb (Nat.mem_primeFactors.mpr ⟨hpbi.1, hpbi.2, (hsq _ hb).ne_zero⟩)

/-- Every tuple prime is coprime to the common multiplier and every padding.
Consequently an absent tuple prime cannot divide a step's displacement. -/
lemma word_prime_support {h : ℕ} {w : List SignedStep}
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding) :
    ∀ p i, (∃ j, j < w.length ∧ TuplePrimeAt w p j) → i < w.length →
      ¬TuplePrimeAt w p i → ¬(p : ℤ) ∣ wordStepDisplacement h w i := by
  intro p i hseen hi hnot
  obtain ⟨j, _, hpj⟩ := hseen
  have hp := hpj.1
  have hdata := hsupport p j hpj
  have ha := List.getElem_mem hi
  have htuple : ¬p ∣ w[i].tuple := by
    intro hdiv
    exact hnot ((tuplePrimeAt_iff_getElem w p i hi).mpr ⟨hp, hdiv⟩)
  rw [wordStepDisplacement_getElem h w i hi]
  exact w[i].prime_not_dvd_displacement h p hp hdata.1 (hdata.2 _ ha) htuple

lemma word_step_nonzero {h : ℕ} {w : List SignedStep} (hh : 0 < h)
    (hq : ∀ a ∈ w, 0 < a.padding) (hd : ∀ a ∈ w, Squarefree a.tuple) :
    ∀ i, i < w.length → wordStepDisplacement h w i ≠ 0 := by
  intro i hi
  rw [wordStepDisplacement_getElem h w i hi]
  have ha := List.getElem_mem hi
  have hq' : (w[i].padding : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hq _ ha))
  have hd' : (w[i].tuple : ℤ) ≠ 0 := by exact_mod_cast (hd _ ha).ne_zero
  have hh' : (h : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  unfold SignedStep.displacement
  split <;> simp_all

/-- The block-interval lemma for actual signed words. All hypotheses concern
admissibility, positivity, survival, or the explicit prime supports. Neither
interval-shaped occurrences nor nonzero subintervals is assumed. -/
theorem PositiveWord.block_geometry {h s J : ℕ} {supply : ℕ → ℕ → Prop}
    {x : ℤ} {w : List SignedStep} (hw : PositiveWord h x w) (hh : 0 < h)
    (hlen : w.length ≤ s) (heligible : ∀ a ∈ w, supply a.tuple a.padding)
    (hq : ∀ a ∈ w, 0 < a.padding) (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x w y → ¬ProhibitedSite h s supply y) :
    TuplePrimeIntervals w ∧
      ∀ a b, a < b → b ≤ w.length → wordDisplacement h (wordSlice w a b) ≠ 0 := by
  have havoid := hw.avoids_prohibitedIntervals hsurvive hlen heligible hchain
  have hinterval := block_occurrence_intervals (TuplePrimeAt w) (wordStepDisplacement h w)
    id x w.length hw.tuplePrime_departure_sum (fun _ _ _ hp => tuplePrime_dvd_step hp)
    (word_prime_support hsupport) havoid
  refine ⟨?_, ?_⟩
  · intro p i j k hij hjk hk hpi hpk
    exact hinterval p i j k (Nat.zero_le _) hij hjk hk hpi hpk
  · intro a b hab hbw
    rw [wordSlice_displacement h w hab.le]
    exact block_nonzero_subintervals (TuplePrimeAt w) (wordStepDisplacement h w) id w.length
      hinterval (fun _ _ _ hp => tuplePrime_dvd_step hp) (word_prime_support hsupport)
      (word_step_nonzero hh hq hsq) (adjacent_tuple_prime_change w J hsq hcard hchain)
      havoid a b hab hbw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations


namespace ColumnWordPattern

variable {α : Type*}




@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]

lemma displacement (w : ColumnWordPattern α) (h : ℕ) (value : α → ℕ)
    (j : ℕ) (hj : j < w.length) :
    wordStepDisplacement h (w.word value) j = w.coefficient h j * value (w.label j) := by
  rw [wordStepDisplacement_getElem h (w.word value) j (by simpa using hj)]
  simp only [word, List.getElem_ofFn, step, SignedStep.displacement, coefficient, Nat.cast_mul]
  ring




end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnWordGeometry
namespace OAI

/-! Nonzero actual word intervals force nonzero quotient-run coefficients. -/

namespace TwoPointCorrelations

open _root_.Finset

namespace ColumnWordPattern

variable {α : Type*}

/-- The coefficient sum of a constant column run cannot vanish when its
actual integer displacement does not vanish. -/
lemma constant_run_coefficient_ne_zero (w : ColumnWordPattern α) (h : ℕ)
    (value : α → ℕ) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ w.length) (z : α)
    (hconst : ∀ t ∈ Ico a b, w.label t = z)
    (hnonzero : wordDisplacement h (wordSlice (w.word value) a b) ≠ 0) :
    (∑ t ∈ Ico a b, w.coefficient h t) ≠ 0 := by
  intro hz
  apply hnonzero
  rw [wordSlice_displacement h (w.word value) hab]
  change (∑ t ∈ Ico a b, wordStepDisplacement h (w.word value) t) = 0
  calc
    _ = ∑ t ∈ Ico a b, w.coefficient h t * (value z : ℤ) := by
      apply sum_congr rfl
      intro t ht
      rw [w.displacement h value t ((mem_Ico.mp ht).2.trans_le hb), hconst t ht]
    _ = (∑ t ∈ Ico a b, w.coefficient h t) * (value z : ℤ) := (sum_mul _ _ _).symm
    _ = 0 := by rw [hz, zero_mul]

lemma constant_run_real_coefficient_ne_zero (w : ColumnWordPattern α) (h : ℕ)
    (value : α → ℕ) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ w.length) (z : α)
    (hconst : ∀ t ∈ Ico a b, w.label t = z)
    (hnonzero : wordDisplacement h (wordSlice (w.word value) a b) ≠ 0) :
    (∑ t ∈ Ico a b, (w.coefficient h t : ℝ)) ≠ 0 := by
  have hn := w.constant_run_coefficient_ne_zero h value a b hab hb z hconst hnonzero
  exact_mod_cast hn


end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBlockGeometry
namespace OAI

/-! The perfect-block geometry for the actual labels of a fixed prime column. -/

namespace TwoPointCorrelations.ColumnWordPattern

open _root_.Finset

variable {α : Type*}

/-- Disjoint column supplies turn numerical prime intervals into intervals
of the abstract labels used by the decoder. -/
theorem label_intervals_of_prime_intervals (w : ColumnWordPattern α) (value : α → ℕ)
    (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    (hinterval : TuplePrimeIntervals (w.word value)) :
    ∀ i j k : Fin w.length, i ≤ j → j ≤ k → w.label i = w.label k → w.label j = w.label i := by
  have hmem (i : Fin w.length) : TuplePrimeAt (w.word value) (value (w.label i)) i := by
    apply (tuplePrimeAt_iff_getElem _ _ i (by simp)).mpr
    refine ⟨hprime _, ?_⟩
    simp [word, step]
  intro i j k hij hjk heq
  have hpk : TuplePrimeAt (w.word value) (value (w.label i)) k := by
    simpa only [heq] using hmem k
  have hpj := hinterval (value (w.label i)) i j k hij hjk (by simp) (hmem i) hpk
  have hdiv := ((tuplePrimeAt_iff_getElem _ _ j (by simp)).mp hpj).2
  simp only [word, List.getElem_ofFn, step] at hdiv
  have hval : value (w.label i) ∣ value (w.label j) :=
    ((hprime _).dvd_mul.mp hdiv).resolve_right (hother _ j j.isLt)
  have he : value (w.label i) = value (w.label j) :=
    (Nat.dvd_prime (hprime _)).mp hval |>.resolve_left (hprime _).ne_one
  exact hvalue he.symm

/-- All block geometry needed for coding follows from the genuine surviving
positive-word lemma, with only the disjoint prime-supply data added. -/
theorem positive_block_geometry (w : ColumnWordPattern α) (value : α → ℕ)
    (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    {h s J : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ}
    (hw : PositiveWord h x (w.word value)) (hh : 0 < h)
    (hlen : w.length ≤ s)
    (heligible : ∀ a ∈ w.word value, supply a.tuple a.padding)
    (hq : ∀ a ∈ w.word value, 0 < a.padding)
    (hsq : ∀ a ∈ w.word value, Squarefree a.tuple)
    (hcard : ∀ a ∈ w.word value, a.tuple.primeFactors.card = J)
    (hchain : (w.word value).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (w.word value) p j →
      ¬p ∣ h ∧ ∀ a ∈ w.word value, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (w.word value) y → ¬ProhibitedSite h s supply y) :
    (∀ i j k : Fin w.length, i ≤ j → j ≤ k → w.label i = w.label k → w.label j = w.label i) ∧
      ∀ a b z, a < b → b ≤ w.length →
        (∀ t ∈ Ico a b, w.label t = z) →
        (∑ t ∈ Ico a b, (w.coefficient h t : ℝ)) ≠ 0 := by
  have hg := hw.block_geometry hh (by simpa using hlen) heligible hq hsq hcard hchain hsupport hsurvive
  refine ⟨w.label_intervals_of_prime_intervals value hvalue hprime hother hg.1, ?_⟩
  intro a b z hab hb hconst
  exact w.constant_run_real_coefficient_ne_zero h value a b hab.le hb z hconst
    (hg.2 a b hab (by simpa using hb))

end TwoPointCorrelations.ColumnWordPattern

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnWordSlices
namespace OAI

/-! Actual contiguous column blocks retain their signed word and coefficient geometry. -/

namespace TwoPointCorrelations.ColumnWordPattern

open _root_.Finset

variable {α : Type*}


theorem slice_word (w : ColumnWordPattern α) (value : α → ℕ) (start len : ℕ)
    (h : start + len ≤ w.length) :
    (w.slice start len).word value = wordSlice (w.word value) start (start + len) := by
  apply List.ext_getElem
  · rw [word_length, wordSlice_length _ (by omega) (by simpa using h)]
    simp only [slice, Nat.add_sub_cancel_left]
  · intro i hi hj
    simp only [word, List.getElem_ofFn, wordSlice, List.getElem_take, List.getElem_drop,
      slice, step]

theorem slice_coefficient (w : ColumnWordPattern α) (h start len t : ℕ) :
    (w.slice start len).coefficient h t = w.coefficient h (start + t) := rfl

/-- Use positivity only on the actual perfect block; other positions in
the full trace word may be unlit. All global admissibility properties are
restricted to that block, and every scalar sum uses its original indices. -/
theorem block_geometry_of_slice (w : ColumnWordPattern α) (value : α → ℕ)
    (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    {h s J : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (start len : ℕ)
    (hend : start + len ≤ w.length) (hshort : len ≤ s)
    (hw : PositiveWord h x (wordSlice (w.word value) start (start + len))) (hh : 0 < h)
    (heligible : ∀ a ∈ w.word value, supply a.tuple a.padding)
    (hq : ∀ a ∈ w.word value, 0 < a.padding)
    (hsq : ∀ a ∈ w.word value, Squarefree a.tuple)
    (hcard : ∀ a ∈ w.word value, a.tuple.primeFactors.card = J)
    (hchain : (wordSlice (w.word value) start (start + len)).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (w.word value) p j →
      ¬p ∣ h ∧ ∀ a ∈ w.word value, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (wordSlice (w.word value) start (start + len)) y →
      ¬ProhibitedSite h s supply y) :
    (∀ i j k : Fin len, i ≤ j → j ≤ k →
      w.label (start + i) = w.label (start + k) → w.label (start + j) = w.label (start + i)) ∧
    (∀ a b z, start ≤ a → a < b → b ≤ start + len →
      (∀ t ∈ Ico a b, w.label t = z) → (∑ t ∈ Ico a b, (w.coefficient h t : ℝ)) ≠ 0) := by
  let u := w.slice start len
  have he : u.word value = wordSlice (w.word value) start (start + len) := w.slice_word value start len hend
  have hsub := (wordSlice_infix (w.word value) start (start + len)).subset
  have hg := u.positive_block_geometry value hvalue hprime
    (fun z t ht => hother z (start + t) (by change t < len at ht; omega))
    (by simpa only [he] using hw) hh hshort
    (fun a ha => heligible a (hsub (he ▸ ha)))
    (fun a ha => hq a (hsub (he ▸ ha)))
    (fun a ha => hsq a (hsub (he ▸ ha)))
    (fun a ha => hcard a (hsub (he ▸ ha)))
    (by rw [he]; exact hchain)
    (by
      intro p j hp
      have hj : j < len := by simpa only [word_length, u, slice] using hp.index_lt
      have hp' : TuplePrimeAt (w.word value) p (start + j) := by
        apply (tuplePrimeAt_slice _ start (start + len) p j (by omega)).mp
        rwa [he] at hp
      have hd := hsupport p (start + j) hp'
      exact ⟨hd.1, fun a ha => hd.2 a (hsub (he ▸ ha))⟩)
    (by simpa only [he] using hsurvive)
  refine ⟨hg.1, ?_⟩
  intro a b z ha hab hb hc
  have hn := hg.2 (a - start) (b - start) z (by omega) (by change b - start ≤ len; omega) (by
    intro t ht
    apply hc
    obtain ⟨hl, hu⟩ := mem_Ico.mp ht
    exact mem_Ico.mpr ⟨by omega, by omega⟩)
  have heq := sum_Ico_add (fun t => (w.coefficient h t : ℝ)) (a - start) (b - start) start
  rw [Nat.sub_add_cancel ha, Nat.sub_add_cancel (by omega : start ≤ b)] at heq
  simpa only [u, slice_coefficient, heq] using hn

end TwoPointCorrelations.ColumnWordPattern

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.IndexedQuotientPaths
namespace OAI

/-! Actual indexed regular pieces give the paths used by the forest decoder. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {K α ι : Type*} [Field K] [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- Forgetting the omitted-label cut retains precisely the original constant
intervals. Renaming regular labels therefore supplies actual quotient run data. -/
theorem indexed_chain_quotient_data (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α) (rename : α → ι)
    (label : ℕ → α) (coefficient : ℕ → K)
    (first : ℕ × α) (rest : List (ℕ × α))
    (hchain : (first :: rest).IsChain (IndexedRunStep label))
    (hname : ∀ p ∈ first :: rest, regularLabel (rename p.2) = p.2)
    (hline : ∀ p ∈ first :: rest,
      ∃ c : K, D.mkQ (formalDeparture label coefficient p.1) = anchor (rename p.2) +
        c • D.mkQ (Pi.basisFun K α (regularLabel (rename p.2))))
    (hnonzero : ∀ p q, p ∈ first :: rest → q ∈ first :: rest → p.1 < q.1 →
      (∀ t ∈ Ico p.1 q.1, label t = p.2) → (∑ t ∈ Ico p.1 q.1, coefficient t) ≠ 0) :
    QuotientRunData D anchor regularLabel label coefficient first.1 (rename first.2)
      (rest.map (fun p => (p.1, rename p.2))) := by
  induction rest generalizing first with
  | nil => trivial
  | cons next rest ih =>
      have hfirst : first ∈ first :: next :: rest := List.mem_cons_self
      have hnext : next ∈ first :: next :: rest := by simp
      rcases hchain.rel with ⟨hlt, _, _, hne, hconst⟩
      refine ⟨hlt.le, ?_, hnonzero first next hfirst hnext hlt hconst, ?_, hline next hnext, ?_⟩
      · intro t ht
        rw [hname first hfirst]
        exact hconst t ht
      · intro heq
        apply hne
        calc
          first.2 = regularLabel (rename first.2) := (hname first hfirst).symm
          _ = regularLabel (rename next.2) := congrArg regularLabel heq
          _ = next.2 := hname next hnext
      · apply ih next hchain.tail
        · intro p hp
          exact hname p (List.mem_cons_of_mem _ hp)
        · intro p hp
          exact hline p (List.mem_cons_of_mem _ hp)
        · intro p q hp hq
          exact hnonzero p q (List.mem_cons_of_mem _ hp) (List.mem_cons_of_mem _ hq)

/-- Every nonempty regular piece produced from an actual block has the
quotient path data. Its transitions are proved from the indexed scan. -/
theorem indexed_regular_piece_quotient_data (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α) (rename : α → ι)
    (label : ℕ → α) (coefficient : ℕ → K) (start len : ℕ)
    (omitted : α → Bool) (first : ℕ × α) (rest : List (ℕ × α))
    (hpiece : Sum.inl (first :: rest) ∈ partitionColumnRuns (fun p => omitted p.2)
      (indexedBlockRuns label start len))
    (hname : ∀ z, omitted z = false → regularLabel (rename z) = z)
    (hline : ∀ t ∈ Ico start (start + len), omitted (label t) = false →
      ∃ c : K, D.mkQ (formalDeparture label coefficient t) = anchor (rename (label t)) +
        c • D.mkQ (Pi.basisFun K α (regularLabel (rename (label t)))))
    (hnonzero : ∀ a b z, start ≤ a → a < b → b ≤ start + len →
      (∀ t ∈ Ico a b, label t = z) → (∑ t ∈ Ico a b, coefficient t) ≠ 0) :
    QuotientRunData D anchor regularLabel label coefficient first.1 (rename first.2)
      (rest.map (fun p => (p.1, rename p.2))) := by
  have hinfix := partitionColumnRuns_regular_infix (fun p => omitted p.2)
    (indexedBlockRuns label start len) (first :: rest) hpiece
  have hmem : ∀ p ∈ first :: rest, p ∈ indexedBlockRuns label start len :=
    fun p hp => hinfix.sublist.subset hp
  have hreg := (partitionColumnRuns_regular_entries (fun p => omitted p.2)
    (indexedBlockRuns label start len) (first :: rest) hpiece).2
  apply indexed_chain_quotient_data D anchor regularLabel rename label coefficient first rest
    (partitionColumnRuns_regular_chain (IndexedRunStep label) _ _ _
      (indexedBlockRuns_chain label start len) hpiece)
  · intro p hp
    exact hname p.2 (hreg p hp)
  · intro p hp
    obtain ⟨hl, hu, he⟩ := indexedBlockRuns_mem label start len p (hmem p hp)
    simpa only [he] using hline p.1 (mem_Ico.mpr ⟨hl, hu⟩) (by rw [he]; exact hreg p hp)
  · intro p q hp hq hpq hconst
    obtain ⟨hl, _, _⟩ := indexedBlockRuns_mem label start len p (hmem p hp)
    obtain ⟨_, hu, _⟩ := indexedBlockRuns_mem label start len q (hmem q hq)
    exact hnonzero p.1 q.1 p.2 hl hpq hu.le hconst

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuotientPathNumbering
namespace OAI

/-! One bounded numbering for the regular lines in all actual quotient paths. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.SimpleGraph

private theorem inl_mem_incidenceVertices {ι V : Type*} (i j : ι) (steps : List (V × ι)) :
    Sum.inl j ∈ incidenceVertices i steps ↔ j ∈ i :: steps.map Prod.snd := by
  induction steps generalizing i with
  | nil => simp [incidenceVertices]
  | cons step rest ih =>
      rcases step with ⟨x, k⟩
      simp [incidenceVertices, ih]

variable {K α ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

/-- The same forest numbering is used for every regular segment. Equal line
numbers therefore identify exactly equal regular labels across all blocks. -/
theorem quotient_run_family_numbering {S N : ℕ}
    (D : Submodule K (α → K)) (anchor : ι → (α → K) ⧸ D)
    (regularLabel : ι → α) (label : ℕ → α) (coefficient : ℕ → K)
    (hind : LinearIndependent K (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))))
    (start : Fin S → ℕ) (first : Fin S → ι) (steps : Fin S → List (ℕ × ι))
    (hstart : ∀ i, ∃ c : K, D.mkQ (formalDeparture label coefficient (start i)) =
      anchor (first i) + c • D.mkQ (Pi.basisFun K α (regularLabel (first i))))
    (hdata : ∀ i, QuotientRunData D anchor regularLabel label coefficient (start i) (first i) (steps i))
    (hsize : (∑ i, (2 * (steps i).length + 1)) ≤ N) :
    ∃ (number : ι → ℕ) (code : ForestPathData.Code N S),
      (∀ i j, j ∈ first i :: (steps i).map Prod.snd → number j < N) ∧
      (∀ i j, j ∈ first i :: (steps i).map Prod.snd →
        ∀ k l, l ∈ first k :: (steps k).map Prod.snd → number j = number l → j = l) ∧
      ∀ i, evenEntries (decodeForestPaths code i) =
        (first i :: (steps i).map Prod.snd).map number := by
  classical
  let direction := fun j => D.mkQ (Pi.basisFun K α (regularLabel j))
  let G := affineIncidenceGraph (K := K) anchor direction
  let vertices := fun i => incidenceVertices (first i) (quotientRunSteps D label coefficient (steps i))
  have hne : ∀ i, vertices i ≠ [] := fun i => incidenceVertices_ne_nil _ _
  have hchain : ∀ i, (vertices i).IsChain G.Adj := fun i =>
    incidenceVertices_isChain anchor direction (first i) _
      (quotientRunData_incidenceChain D anchor regularLabel label coefficient
        (start i) (first i) (steps i) (hstart i) (hdata i))
  let starts := fun i => (vertices i).head (hne i)
  let finishes := fun i => (vertices i).getLast (hne i)
  let walk : ∀ i, G.Walk (starts i) (finishes i) := fun i =>
    Walk.ofSupport (vertices i) (hne i) (hchain i)
  have hsupport (i : Fin S) : (walk i).support = vertices i :=
    Walk.support_ofSupport (G := G) (hne i) (hchain i)
  have hG : G.IsAcyclic := affineIncidenceGraph_isAcyclic anchor direction hind
  have hred : ∀ i, List.IsChain (· ≠ ·) (walk i).edges := by
    intro i
    apply (hG.isPath_iff_isChain _).mp
    exact quotientRunData_simple D anchor regularLabel label coefficient hind
      (start i) (first i) (steps i) (hstart i) (hdata i)
  have hsize' : (∑ i, (walk i).support.length) ≤ N := by
    simp_rw [hsupport]
    simpa only [vertices, incidenceVertices_length, quotientRunSteps, List.length_map] using hsize
  obtain ⟨number, code, hinj, hbound, hdecode⟩ :=
    finite_walk_family_numbering starts finishes walk hG hred hsize'
      (Sum.elim (fun _ => true) (fun _ => false))
  have hmem : ∀ i j, j ∈ first i :: (steps i).map Prod.snd →
      Sum.inl j ∈ walkFamilySupport starts finishes walk := by
    intro i j hj
    apply mem_walkFamilySupport starts finishes walk i
    rw [hsupport]
    apply (inl_mem_incidenceVertices _ _ _).mpr
    simpa only [quotientRunSteps, List.map_map, Function.comp_def] using hj
  refine ⟨fun j => number (.inl j), code, ?_, ?_, ?_⟩
  · intro i j hj
    exact hbound _ (hmem i j hj)
  · intro i j hj k l hl heq
    exact Sum.inl.inj (hinj (hmem i j hj) (hmem k l hl) heq)
  · intro i
    rw [hdecode]
    rw [hsupport]
    rw [evenEntries_incidenceVertices]
    simp only [quotientRunSteps, List.map_map, Function.comp_def]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RegularSegmentCoding
namespace OAI

/-! Assemble all actual regular segments into one shared forest code. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {K α ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

/-- Enumerating nonempty segments does not require separate choices of line
names for each block. Their common quotient forest supplies one numbering. -/
theorem regular_segment_list_numbering {N : ℕ}
    (D : Submodule K (α → K)) (anchor : ι → (α → K) ⧸ D)
    (regularLabel : ι → α) (label : ℕ → α) (coefficient : ℕ → K)
    (hind : LinearIndependent K (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))))
    (segments : List (List (ℕ × ι)))
    (hne : ∀ segment ∈ segments, segment ≠ [])
    (hstart : ∀ first rest, first :: rest ∈ segments → ∃ c : K,
      D.mkQ (formalDeparture label coefficient first.1) =
        anchor first.2 + c • D.mkQ (Pi.basisFun K α (regularLabel first.2)))
    (hdata : ∀ first rest, first :: rest ∈ segments →
      QuotientRunData D anchor regularLabel label coefficient first.1 first.2 rest)
    (hsize : 2 * (segments.map List.length).sum ≤ N) :
    ∃ (number : ι → ℕ) (code : ForestPathData.Code N segments.length),
      (∀ segment ∈ segments, ∀ p ∈ segment, number p.2 < N) ∧
      (∀ segment ∈ segments, ∀ p ∈ segment, ∀ other ∈ segments, ∀ q ∈ other,
        number p.2 = number q.2 → p.2 = q.2) ∧
      List.ofFn (fun i => evenEntries (decodeForestPaths code i)) =
        segments.map (fun segment => segment.map (fun p => number p.2)) := by
  let seg : Fin segments.length → List (ℕ × ι) := segments.get
  have hseg (i : Fin segments.length) : seg i ∈ segments := List.get_mem _ _
  let first := fun i => (seg i).head (hne _ (hseg i))
  let rest := fun i => (seg i).tail
  have hsplit (i : Fin segments.length) : first i :: rest i = seg i :=
    List.cons_head_tail (hne _ (hseg i))
  have hmem (i : Fin segments.length) : first i :: rest i ∈ segments := by
    rw [hsplit]; exact hseg i
  have hs : (∑ i, (2 * (rest i).length + 1)) ≤ N := by
    apply le_trans (sum_le_sum (fun i _ => ?_))
      ((show (∑ i, 2 * (seg i).length) = 2 * (segments.map List.length).sum by
        rw [← mul_sum]
        congr 1
        rw [← List.sum_ofFn]
        change (List.ofFn (List.length ∘ segments.get)).sum = _
        rw [← List.map_ofFn, List.ofFn_get]).le.trans hsize)
    have hl := congrArg List.length (hsplit i)
    simp only [List.length_cons] at hl
    omega
  obtain ⟨number, code, hbound, hinj, hdecode⟩ :=
    quotient_run_family_numbering D anchor regularLabel label coefficient hind
      (fun i => (first i).1) (fun i => (first i).2) rest
      (fun i => hstart _ _ (hmem i)) (fun i => hdata _ _ (hmem i)) hs
  have hlabels (i : Fin segments.length) :
      (first i).2 :: (rest i).map Prod.snd = (seg i).map Prod.snd := by
    rw [← hsplit i]; rfl
  refine ⟨number, code, ?_, ?_, ?_⟩
  · intro segment hm p hp
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hm
    apply hbound i p.2
    rw [hlabels]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · intro segment hm p hp other ho q hq heq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hm
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ho
    apply hinj i p.2 _ j q.2 _ heq
    · rw [hlabels]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    · rw [hlabels]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  · calc
      _ = List.ofFn (fun i => (seg i).map (fun p => number p.2)) := by
        congr 1
        funext i
        rw [hdecode, hlabels, List.map_map]
        rfl
      _ = _ := by
        change List.ofFn ((fun segment => segment.map (fun p => number p.2)) ∘ segments.get) = _
        rw [← List.map_ofFn, List.ofFn_get]

omit [Field K] [Fintype α] [DecidableEq ι] in
/-- Removing omitted runs cannot increase the total number of regular
vertices, even when a label is repeated in separate blocks. -/
theorem regular_pieces_total_length_le (pieces : List (List α ⊕ α)) :
    ((pieces.filterMap (Sum.elim some (fun _ => none))).map List.length).sum ≤
      (pieces.flatMap (Sum.elim id List.singleton)).length := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece with
      | inl segment => simpa using Nat.add_le_add_left ih segment.length
      | inr a =>
          simp only [List.filterMap_cons, Sum.elim_inr, List.flatMap_cons, List.length_append]
          simpa only [List.singleton, List.length_cons, List.length_nil, Nat.add_zero] using
            (ih.trans (Nat.le_add_left _ 1))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.IndexedBlockFamily
namespace OAI

/-! The actual indexed regular segments of a finite family of perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

private theorem decoded_forest_transport {N S T : ℕ} (h : S = T)
    (code : ForestPathData.Code N S) :
    List.ofFn (fun i => evenEntries (decodeForestPaths (h ▸ code) i)) =
      List.ofFn (fun i => evenEntries (decodeForestPaths code i)) := by
  cases h
  rfl

variable {α : Type*} [DecidableEq α]


theorem mem_indexedRegularSegments (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) (segment : List (ℕ × α)) :
    segment ∈ indexedRegularSegments label omitted blocks ↔
      ∃ b ∈ blocks, Sum.inl segment ∈
        partitionColumnRuns (fun p => omitted p.2) (indexedBlockRuns label b.1 b.2) := by
  simp only [indexedRegularSegments, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, piece, hp, he⟩
    cases piece with
    | inl s => cases he; exact ⟨b, hb, hp⟩
    | inr z => simp at he
  · rintro ⟨b, hb, hs⟩
    exact ⟨b, hb, .inl segment, hs, rfl⟩

theorem indexedRegularSegments_nonempty (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) (segment : List (ℕ × α))
    (hs : segment ∈ indexedRegularSegments label omitted blocks) : segment ≠ [] := by
  obtain ⟨b, _, hb⟩ := (mem_indexedRegularSegments label omitted blocks segment).mp hs
  exact (partitionColumnRuns_regular_entries _ _ _ hb).1

theorem indexedBlockRuns_length_le (label : ℕ → α) (start len : ℕ) :
    (indexedBlockRuns label start len).length ≤ len := by
  have h := columnRunHeads_length_le ((blockLabelList label start len).map some) none
  rw [← indexedBlockRuns_labels] at h
  simpa only [List.length_map, blockLabelList, List.length_range] using h

/-- The total number of retained regular run starts is bounded by the
number of original positions, with no factor for the number of labels. -/
theorem indexedRegularSegments_total_length (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) :
    ((indexedRegularSegments label omitted blocks).map List.length).sum ≤
      (blocks.map Prod.snd).sum := by
  induction blocks with
  | nil => rfl
  | cons b blocks ih =>
      have hb := regular_pieces_total_length_le
        (partitionColumnRuns (fun p => omitted p.2) (indexedBlockRuns label b.1 b.2))
      rw [partitionColumnRuns_flatten] at hb
      have hb' := hb.trans (indexedBlockRuns_length_le label b.1 b.2)
      simpa only [indexedRegularSegments, List.flatMap_cons, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons] using Nat.add_le_add hb' ih

/-- Every regular label seen in a block survives both compression and the
omitted-label cut, so its forest line is included in the shared numbering. -/
theorem indexedRegularSegments_cover (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) (b : ℕ × ℕ) (hb : b ∈ blocks) (z : α)
    (hz : z ∈ blockLabelList label b.1 b.2) (hregular : omitted z = false) :
    ∃ segment ∈ indexedRegularSegments label omitted blocks, ∃ p ∈ segment, p.2 = z := by
  have hr := mem_columnRunHeads _ z hz
  rw [← indexedBlockRuns_labels] at hr
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hr
  obtain ⟨segment, hs, hps⟩ := partitionColumnRuns_regular_cover
    (fun p : ℕ × α => omitted p.2) (indexedBlockRuns label b.1 b.2) p hp (by rw [he]; exact hregular)
  exact ⟨segment, (mem_indexedRegularSegments label omitted blocks segment).mpr ⟨b, hb, hs⟩,
    p, hps, he⟩

variable {K ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

/-- Number the regular paths actually produced by the given blocks.
The hypotheses are line incidence and nonvanishing physical intervals;
all path, compression, coverage and size data are constructed here. -/
theorem indexed_block_family_numbering {N : ℕ}
    (D : Submodule K (α → K)) (anchor : ι → (α → K) ⧸ D)
    (regularLabel : ι → α) (rename : α → ι)
    (label : ℕ → α) (coefficient : ℕ → K) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ))
    (hind : LinearIndependent K (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))))
    (hname : ∀ z, omitted z = false → regularLabel (rename z) = z)
    (hline : ∀ b ∈ blocks, ∀ t ∈ Ico b.1 (b.1 + b.2), omitted (label t) = false →
      ∃ c : K, D.mkQ (formalDeparture label coefficient t) = anchor (rename (label t)) +
        c • D.mkQ (Pi.basisFun K α (regularLabel (rename (label t)))))
    (hnonzero : ∀ b ∈ blocks, ∀ a e z, b.1 ≤ a → a < e → e ≤ b.1 + b.2 →
      (∀ t ∈ Ico a e, label t = z) → (∑ t ∈ Ico a e, coefficient t) ≠ 0)
    (hsize : 2 * (blocks.map Prod.snd).sum ≤ N) :
    ∃ (number : ι → ℕ)
      (code : ForestPathData.Code N (indexedRegularSegments label omitted blocks).length),
      (∀ segment ∈ indexedRegularSegments label omitted blocks,
        ∀ p ∈ segment, number (rename p.2) < N) ∧
      (∀ segment ∈ indexedRegularSegments label omitted blocks, ∀ p ∈ segment,
        ∀ other ∈ indexedRegularSegments label omitted blocks, ∀ q ∈ other,
        number (rename p.2) = number (rename q.2) → p.2 = q.2) ∧
      List.ofFn (fun i => evenEntries (decodeForestPaths code i)) =
        (indexedRegularSegments label omitted blocks).map
          (fun segment => segment.map (fun p => number (rename p.2))) := by
  let segments := indexedRegularSegments label omitted blocks
  let relabel := fun p : ℕ × α => (p.1, rename p.2)
  let renamed := segments.map (List.map relabel)
  have hreg : ∀ segment ∈ segments, ∀ p ∈ segment, omitted p.2 = false := by
    intro segment hs p hp
    obtain ⟨b, _, hb⟩ := (mem_indexedRegularSegments label omitted blocks segment).mp hs
    exact (partitionColumnRuns_regular_entries _ _ _ hb).2 p hp
  have horigin : ∀ first rest, first :: rest ∈ renamed →
      ∃ p ps b, p :: ps ∈ segments ∧ b ∈ blocks ∧
        Sum.inl (p :: ps) ∈ partitionColumnRuns (fun p => omitted p.2)
          (indexedBlockRuns label b.1 b.2) ∧ first = relabel p ∧ rest = ps.map relabel := by
    intro first rest hs
    obtain ⟨segment, hsegment, he⟩ := List.mem_map.mp hs
    cases segment with
    | nil => simp at he
    | cons p ps =>
        obtain ⟨b, hb, hp⟩ := (mem_indexedRegularSegments label omitted blocks _).mp hsegment
        simp only [List.map_cons, List.cons.injEq] at he
        exact ⟨p, ps, b, hsegment, hb, hp, he.1.symm, he.2.symm⟩
  have hne : ∀ segment ∈ renamed, segment ≠ [] := by
    intro segment hs
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hs
    intro he
    exact indexedRegularSegments_nonempty label omitted blocks original ho (List.eq_nil_of_map_eq_nil he)
  have hstart : ∀ first rest, first :: rest ∈ renamed → ∃ c : K,
      D.mkQ (formalDeparture label coefficient first.1) =
        anchor first.2 + c • D.mkQ (Pi.basisFun K α (regularLabel first.2)) := by
    intro first rest hs
    obtain ⟨p, ps, b, _, hb, hp, rfl, _⟩ := horigin first rest hs
    have hm := (partitionColumnRuns_regular_infix _ _ _ hp).subset (List.mem_cons_self)
    obtain ⟨hl, hu, he⟩ := indexedBlockRuns_mem label b.1 b.2 p hm
    simpa only [relabel, he] using hline b hb p.1 (mem_Ico.mpr ⟨hl, hu⟩)
      (by rw [he]; exact (partitionColumnRuns_regular_entries _ _ _ hp).2 p List.mem_cons_self)
  have hdata : ∀ first rest, first :: rest ∈ renamed →
      QuotientRunData D anchor regularLabel label coefficient first.1 first.2 rest := by
    intro first rest hs
    obtain ⟨p, ps, b, _, hb, hp, rfl, rfl⟩ := horigin first rest hs
    exact indexed_regular_piece_quotient_data D anchor regularLabel rename label coefficient
      b.1 b.2 omitted p ps hp hname (hline b hb) (hnonzero b hb)
  have hbudget : 2 * (renamed.map List.length).sum ≤ N := by
    have h := Nat.mul_le_mul_left 2 (indexedRegularSegments_total_length label omitted blocks)
    simpa only [renamed, List.map_map, List.length_map, Function.comp_def] using h.trans hsize
  obtain ⟨number, code, hbound, hinj, hdecode⟩ := regular_segment_list_numbering D anchor
    regularLabel label coefficient hind renamed hne hstart hdata hbudget
  have hrenamedLength : renamed.length = segments.length := List.length_map (List.map relabel)
  let code' : ForestPathData.Code N segments.length := hrenamedLength ▸ code
  have hcode : List.ofFn (fun i => evenEntries (decodeForestPaths code' i)) =
      segments.map (fun segment => segment.map (fun p => number (rename p.2))) := by
    change List.ofFn (fun i => evenEntries (decodeForestPaths (hrenamedLength ▸ code) i)) = _
    rw [decoded_forest_transport]
    simpa only [renamed, List.map_map, relabel, Function.comp_def] using hdecode
  refine ⟨number, code', ?_, ?_, hcode⟩
  · intro segment hs p hp
    exact hbound (segment.map relabel) (List.mem_map.mpr ⟨segment, hs, rfl⟩)
      (relabel p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  · intro segment hs p hp other ho q hq he
    have hr := hinj (segment.map relabel) (List.mem_map.mpr ⟨segment, hs, rfl⟩)
      (relabel p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      (other.map relabel) (List.mem_map.mpr ⟨other, ho, rfl⟩)
      (relabel q) (List.mem_map.mpr ⟨q, hq, rfl⟩) he
    exact (hname p.2 (hreg segment hs p hp)).symm.trans
      ((congrArg regularLabel hr).trans (hname q.2 (hreg other ho q hq)))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockFamilyDecoding
namespace OAI

/-! Identify the shared indexed path family with the actual decoder pieces. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

theorem columnChunkPieces_via_blocks (omitted : α → Bool) (chunks : List (List α ⊕ α)) :
    columnChunkPieces omitted chunks =
      (chunks.filterMap (Sum.elim some (fun _ => none))).flatMap
        (fun block => partitionColumnRuns omitted (columnRunHeads (block.map some) none)) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      cases chunk with
      | inl block =>
          simpa only [columnChunkPieces, List.flatMap_cons, List.filterMap_cons, Sum.elim_inl] using
            congrArg (fun rest => partitionColumnRuns omitted
              (columnRunHeads (block.map some) none) ++ rest) ih
      | inr a =>
          simpa only [columnChunkPieces, List.flatMap_cons, List.filterMap_cons,
            Sum.elim_inr, List.nil_append] using ih

theorem columnChunkPieces_from_intervals (label : ℕ → α) (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList label b.1 b.2)) :
    columnChunkPieces omitted chunks = blocks.flatMap (fun b =>
      partitionColumnRuns omitted (columnRunHeads ((blockLabelList label b.1 b.2).map some) none)) := by
  rw [columnChunkPieces_via_blocks, hblocks, List.flatMap_map]

/-- Forgetting the stored run-start indices gives exactly the regular
piece list consumed by the column decoder, in the same order. -/
theorem indexedRegularSegments_labels (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) :
    (indexedRegularSegments label omitted blocks).map (List.map Prod.snd) =
      (blocks.flatMap (fun b => partitionColumnRuns omitted
        (columnRunHeads ((blockLabelList label b.1 b.2).map some) none))).filterMap
          (Sum.elim some (fun _ => none)) := by
  induction blocks with
  | nil => rfl
  | cons b blocks ih =>
      change ((_ ++ indexedRegularSegments label omitted blocks).map (List.map Prod.snd)) = _
      rw [List.map_append]
      simp only [List.flatMap_cons, List.filterMap_append]
      rw [ih]
      congr 1
      rw [← mapped_pieces_regular, indexedBlockRuns_partition]

theorem indexedRegularSegments_eq_regular_pieces (label : ℕ → α) (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList label b.1 b.2)) :
    (indexedRegularSegments label omitted blocks).map (List.map Prod.snd) =
      (columnChunkPieces omitted chunks).filterMap (Sum.elim some (fun _ => none)) := by
  rw [columnChunkPieces_from_intervals label omitted chunks blocks hblocks]
  exact indexedRegularSegments_labels label omitted blocks

omit [DecidableEq α] in
/-- Every original perfect occurrence belongs to one of the actual perfect
blocks. This includes occurrences immediately next to imperfect positions. -/
theorem perfect_entry_mem_block (chunks : List (List α ⊕ α)) (a : α)
    (ha : (a, true) ∈ columnChunkEntries chunks) :
    ∃ block, Sum.inl block ∈ chunks ∧ a ∈ block := by
  obtain ⟨chunk, hc, ha⟩ := List.mem_flatMap.mp ha
  cases chunk with
  | inl block =>
      obtain ⟨b, hb, heq⟩ := List.mem_map.mp ha
      have he : b = a := congrArg Prod.fst heq
      exact ⟨block, hc, he ▸ hb⟩
  | inr b =>
      have heq := List.mem_singleton.mp ha
      have hfalse : false = true := (congrArg Prod.snd heq).symm
      contradiction

/-- Every regular perfect label appears in the actual indexed path family. -/
theorem perfect_regular_entry_covered (label : ℕ → α) (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList label b.1 b.2))
    (a : α) (ha : (a, true) ∈ columnChunkEntries chunks) (hr : omitted a = false) :
    ∃ segment ∈ indexedRegularSegments label omitted blocks, ∃ p ∈ segment, p.2 = a := by
  obtain ⟨block, hb, hab⟩ := perfect_entry_mem_block chunks a ha
  have hm : block ∈ chunks.filterMap (Sum.elim some (fun _ => none)) :=
    List.mem_filterMap.mpr ⟨.inl block, hb, rfl⟩
  rw [hblocks] at hm
  obtain ⟨b, hbb, he⟩ := List.mem_map.mp hm
  apply indexedRegularSegments_cover label omitted blocks b hbb a _ hr
  rwa [he]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RegularFamilyNames
namespace OAI

/-! Every regular perfect class inherits the bounds and injectivity of its forest line. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α] {n N : ℕ}

omit [DecidableEq α] in
theorem perfect_label_entry (label : Fin n → α) (perfect : Finset (Fin n))
    (chunks : List (List α ⊕ α))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (i : Fin n) (hi : i ∈ perfect) : (label i, true) ∈ columnChunkEntries chunks := by
  rw [hentries]
  simp only [columnPositionEntries, List.map_ofFn, Function.comp_def]
  apply List.mem_ofFn.mpr
  exact ⟨i, by simp [hi]⟩

omit [DecidableEq α] in
theorem perfect_label_position (label : Fin n → α) (perfect : Finset (Fin n))
    (chunks : List (List α ⊕ α))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (a : α) (ha : (a, true) ∈ columnChunkEntries chunks) :
    ∃ i ∈ perfect, label i = a := by
  rw [hentries] at ha
  simp only [columnPositionEntries, List.map_ofFn, Function.comp_def, List.mem_ofFn] at ha
  obtain ⟨i, he⟩ := ha
  have hlabel : label i = a := congrArg Prod.fst he
  have hperfect : decide (i ∈ perfect) = true := congrArg Prod.snd he
  exact ⟨i, of_decide_eq_true hperfect, hlabel⟩

/-- Coverage makes the shared forest bounds and injectivity apply to every
perfect regular occurrence, including those suppressed by run compression. -/
theorem regular_family_name_properties (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (lineNumber : α → ℕ)
    (hnumber : ∀ z (hz : z ∈ regular), lineNumber z = number ⟨z, hz⟩)
    (labelNat : ℕ → α)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList labelNat b.1 b.2))
    (hbound : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ p ∈ segment, lineNumber p.2 < N)
    (hinj : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ p ∈ segment,
      ∀ other ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ q ∈ other, lineNumber p.2 = lineNumber q.2 → p.2 = q.2) :
    (∀ i ∈ perfect, ∀ hi : label i ∈ regular, number ⟨label i, hi⟩ < N) ∧
    (∀ i ∈ perfect, ∀ j ∈ perfect, ∀ (hi : label i ∈ regular) (hj : label j ∈ regular),
      number ⟨label i, hi⟩ = number ⟨label j, hj⟩ → label i = label j) := by
  have hcover (i : Fin n) (hi : i ∈ perfect) (hr : label i ∈ regular) :
      ∃ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
        ∃ p ∈ segment, p.2 = label i := by
    exact perfect_regular_entry_covered labelNat (fun z => decide (z ∉ regular)) chunks blocks
      hblocks (label i) (perfect_label_entry label perfect chunks hentries i hi) (by simp [hr])
  have hnamed (i : Fin n) (hi : label i ∈ regular) (p : ℕ × α) (hp : p.2 = label i) :
      lineNumber p.2 = number ⟨label i, hi⟩ := by
    rw [hp]
    exact hnumber (label i) hi
  constructor
  · intro i hi hr
    obtain ⟨segment, hs, p, hp, he⟩ := hcover i hi hr
    simpa only [hnamed i hr p he] using hbound segment hs p hp
  · intro i hi j hj hri hrj heq
    obtain ⟨segment, hs, p, hp, hpi⟩ := hcover i hi hri
    obtain ⟨other, ho, q, hq, hqj⟩ := hcover j hj hrj
    have he : lineNumber p.2 = lineNumber q.2 := by
      simpa only [hnamed i hri p hpi, hnamed j hrj q hqj] using heq
    exact hpi.symm.trans ((hinj segment hs p hp other ho q hq he).trans hqj)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnForestAssembly
namespace OAI

/-! Assemble an actual column code from the shared forest of its regular paths. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

theorem column_code_from_regular_forest {n N O I : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (lineNumber : α → ℕ)
    (hnumber : ∀ z (hz : z ∈ regular), lineNumber z = number ⟨z, hz⟩)
    (labelNat : ℕ → α)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList labelNat b.1 b.2))
    (pathCode : ForestPathData.Code N
      (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length)
    (hbound : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ p ∈ segment, lineNumber p.2 < N)
    (hinj : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ p ∈ segment,
      ∀ other ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ q ∈ other, lineNumber p.2 = lineNumber q.2 → p.2 = q.2)
    (hdecode : List.ofFn (fun i => evenEntries (decodeForestPaths pathCode i)) =
      (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).map
        (fun segment => segment.map (fun p => lineNumber p.2)))
    (hO : omittedPieceCount (columnChunkPieces (fun z => decide (z ∉ regular)) chunks) ≤ O)
    (hI : ((columnPositionEntries perfect).filter (fun a => !a.2)).length ≤ I) :
    ∃ code : ColumnDecoderCode N
        (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length O I,
      (decodeColumnLabels code).take n =
        List.ofFn (canonicalColumnName label perfect (forestPerfectName label perfect regular number)) ∧
      decodeColumnPrefixPattern hn code = (fun i j => decide (label i = label j)) := by
  let isOmitted := fun z : α => decide (z ∉ regular)
  let segments := indexedRegularSegments labelNat isOmitted blocks
  let names := forestPerfectName label perfect regular number
  let f := observedColumnName label perfect names
  let raw := columnChunkPieces isOmitted chunks
  let pieces := raw.map (Sum.map (List.map f) f)
  let namedChunks := chunks.map (Sum.map (List.map f) f)
  let cuts := columnChunkCuts namedChunks
  have hprops := regular_family_name_properties label perfect regular number lineNumber hnumber
    labelNat chunks blocks hentries hblocks hbound hinj
  have heq (i j : Fin n) : f (label i) = f (label j) ↔ label i = label j :=
    observed_forest_name_eq_iff label perfect regular number hprops.2 i j
  have hlocal : ∀ block, Sum.inl block ∈ chunks →
      ∀ a ∈ block, ∀ b ∈ block, f a = f b ↔ a = b := by
    intro block hb a ha b hbb
    have ha' : (a, true) ∈ columnChunkEntries chunks :=
      List.mem_flatMap.mpr ⟨.inl block, hb, List.mem_map.mpr ⟨a, ha, rfl⟩⟩
    have hb' : (b, true) ∈ columnChunkEntries chunks :=
      List.mem_flatMap.mpr ⟨.inl block, hb, List.mem_map.mpr ⟨b, hbb, rfl⟩⟩
    obtain ⟨i, _, hi⟩ := perfect_label_position label perfect chunks hentries a ha'
    obtain ⟨j, _, hj⟩ := perfect_label_position label perfect chunks hentries b hb'
    simpa only [hi, hj] using heq i j
  have hcuts : cuts.map Prod.fst = canonicalPerfectEntries label perfect names := by
    change (columnChunkCuts namedChunks).map Prod.fst = _
    rw [columnChunkCuts_values]
    change (columnChunkEntries (chunks.map (Sum.map (List.map f) f))).map _ = _
    rw [columnChunkEntries_map, hentries]
    simp only [columnPositionEntries, List.map_ofFn, canonicalPerfectEntries,
      Function.comp_def]
    congr 1
    funext i
    by_cases hi : i ∈ perfect <;> simp [f, observedColumnName_at, hi]
  have hpieces : pieces.length ≤ N := by
    change (raw.map _).length ≤ N
    rw [List.length_map]
    apply (columnChunkPieces_length_le isOmitted chunks).trans
    rw [hentries, List.length_map]
    simpa only [columnPositionEntries, List.length_ofFn] using hn
  have hlabels : segments.map (List.map Prod.snd) =
      raw.filterMap (Sum.elim some (fun _ => none)) :=
    indexedRegularSegments_eq_regular_pieces labelNat isOmitted chunks blocks hblocks
  have hregularName : ∀ segment ∈ segments, ∀ p ∈ segment,
      f p.2 = .regular (lineNumber p.2) := by
    intro segment hs p hp
    have hs' : segment.map Prod.snd ∈ raw.filterMap (Sum.elim some (fun _ => none)) := by
      rw [← hlabels]
      exact List.mem_map.mpr ⟨segment, hs, rfl⟩
    obtain ⟨piece, hpiece, hs'⟩ := List.mem_filterMap.mp hs'
    have hinl : Sum.inl (segment.map Prod.snd) ∈ raw := by
      cases piece with
      | inl l => cases hs'; exact hpiece
      | inr a => simp at hs'
    have hm := (columnChunkPieces_regular_membership isOmitted chunks _ hinl).2 p.2
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hr : p.2 ∈ regular := by simpa only [isOmitted, decide_eq_false_iff_not, not_not] using hm.1
    obtain ⟨i, hip, hi⟩ := perfect_label_position label perfect chunks hentries p.2 hm.2
    have hir : label i ∈ regular := hi.symm ▸ hr
    have hn' : lineNumber p.2 = number ⟨label i, hir⟩ := by
      rw [← hi]
      exact hnumber (label i) hir
    calc
      f p.2 = f (label i) := congrArg f hi.symm
      _ = .regular (number ⟨label i, hir⟩) := observed_forest_name_regular label perfect regular number i hip hir
      _ = _ := congrArg CanonicalColumnLabel.regular hn'.symm
  have hregular : List.ofFn (fun i => (evenEntries (decodeForestPaths pathCode i)).map
      CanonicalColumnLabel.regular) = pieces.filterMap (Sum.elim some (fun _ => none)) := by
    have hd := congrArg (List.map (List.map CanonicalColumnLabel.regular)) hdecode
    simp only [List.map_ofFn, List.map_map, Function.comp_def] at hd
    calc
      _ = segments.map (fun segment => segment.map (fun p => .regular (lineNumber p.2))) := hd
      _ = segments.map (fun segment => segment.map (fun p => f p.2)) := by
        apply List.map_congr_left
        intro segment hs
        apply List.map_congr_left
        intro p hp
        exact (hregularName segment hs p hp).symm
      _ = (segments.map (List.map Prod.snd)).map (List.map f) := by
        simp only [List.map_map, Function.comp_def]
      _ = (raw.filterMap (Sum.elim some (fun _ => none))).map (List.map f) := by rw [hlabels]
      _ = _ := (mapped_pieces_regular f raw).symm
  have homit : ∀ a ∈ pieces.filterMap (Sum.elim (fun _ => none) some),
      ∃ j : Fin N, a = .omitted j.val := by
    intro a ha
    change a ∈ (raw.map (Sum.map (List.map f) f)).filterMap _ at ha
    rw [mapped_pieces_omitted] at ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    obtain ⟨piece, hp, hz⟩ := List.mem_filterMap.mp hz
    have hinr : Sum.inr z ∈ raw := by
      cases piece with
      | inl l => simp at hz
      | inr b => cases hz; exact hp
    have hm := columnChunkPieces_omitted_membership isOmitted chunks z hinr
    have hr : z ∉ regular := of_decide_eq_true hm.1
    obtain ⟨i, hip, hi⟩ := perfect_label_position label perfect chunks hentries z hm.2
    have hir : label i ∉ regular := hi.symm ▸ hr
    refine ⟨Fin.castLE hn (columnRepresentative label perfect i), ?_⟩
    simpa only [f, names, hi, Fin.val_castLE] using
      observed_forest_name_omitted label perfect regular number i hip hir
  obtain ⟨omittedNames, holen, homap⟩ := omitted_names_lift _ homit
  have ho : omittedNames.length ≤ O := by
    rw [holen]
    change ((raw.map (Sum.map (List.map f) f)).filterMap _).length ≤ O
    rw [mapped_pieces_omitted, List.length_map]
    exact hO
  have hheads : pieces.flatMap (Sum.elim id List.singleton) = columnRunHeadsWithCuts cuts none :=
    mapped_column_pieces_heads f isOmitted chunks hlocal
  obtain ⟨code, hprefix⟩ := canonical_column_encoding hN hn label perfect names pathCode cuts hcuts pieces hpieces []
    (by simpa only [List.append_nil] using hregular) omittedNames ho homap.symm hheads hI
  exact ⟨code, hprefix, column_prefix_pattern_recovers hn code label _ hprefix
    (canonical_forest_name_eq_iff label perfect regular number hprops.2)⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnGeometryEncoding
namespace OAI

/-! From quotient-line geometry to a complete column code, including the empty regular set. -/

namespace TwoPointCorrelations

open _root_.Finset

private theorem partition_all_omitted {α : Type*} (runs : List α) :
    partitionColumnRuns (fun _ => true) runs = runs.map Sum.inr := by
  induction runs with
  | nil => rfl
  | cons a runs ih => simp only [partitionColumnRuns, ite_true, List.map_cons, ih]

theorem indexedRegularSegments_eq_nil {α : Type*} [DecidableEq α]
    (label : ℕ → α) (omitted : α → Bool) (blocks : List (ℕ × ℕ))
    (h : ∀ z, omitted z = true) : indexedRegularSegments label omitted blocks = [] := by
  have ho : omitted = fun _ => true := funext h
  subst omitted
  have hp (runs : List (ℕ × α)) :
      (partitionColumnRuns (fun _ => true) runs).filterMap (Sum.elim some (fun _ => none)) = [] := by
    rw [partition_all_omitted]
    simp only [List.filterMap_map, Function.comp_def, Sum.elim_inr, List.filterMap_eq_nil_iff]
    simp
  apply List.flatMap_eq_nil_iff.mpr
  intro b _
  exact hp _


/-- The only geometric premises are independent quotient directions,
actual line incidence, and nonzero constant intervals. All path codes,
canonical labels, occurrence references and the full equality pattern are
constructed. No nonemptiness of the regular set is required. -/
theorem column_code_from_quotient_geometry {α : Type*} [Fintype α] [DecidableEq α]
    {n N O I : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (label : Fin n → α) (perfect : Finset (Fin n)) (regular : Finset α)
    (labelNat : ℕ → α) (coefficient : ℕ → ℝ)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList labelNat b.1 b.2))
    (D : Submodule ℝ (α → ℝ)) (anchor : regular → (α → ℝ) ⧸ D)
    (hind : LinearIndependent ℝ (fun z : regular => D.mkQ (Pi.basisFun ℝ α z)))
    (hline : ∀ b ∈ blocks, ∀ t ∈ Ico b.1 (b.1 + b.2), ∀ ht : labelNat t ∈ regular,
      ∃ c : ℝ, D.mkQ (formalDeparture labelNat coefficient t) = anchor ⟨labelNat t, ht⟩ +
        c • D.mkQ (Pi.basisFun ℝ α (labelNat t)))
    (hnonzero : ∀ b ∈ blocks, ∀ a e z, b.1 ≤ a → a < e → e ≤ b.1 + b.2 →
      (∀ t ∈ Ico a e, labelNat t = z) → (∑ t ∈ Ico a e, coefficient t) ≠ 0)
    (hsize : 2 * (blocks.map Prod.snd).sum ≤ N)
    (hO : omittedPieceCount (columnChunkPieces (fun z => decide (z ∉ regular)) chunks) ≤ O)
    (hI : ((columnPositionEntries perfect).filter (fun a => !a.2)).length ≤ I) :
    ∃ code : ColumnDecoderCode N
        (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length O I,
      decodeColumnPrefixPattern hn code = fun i j => decide (label i = label j) := by
  classical
  by_cases hR : regular.Nonempty
  · let base : regular := ⟨hR.choose, hR.choose_spec⟩
    let rename : α → regular := fun z => if hz : z ∈ regular then ⟨z, hz⟩ else base
    have hrename (z : α) (hz : z ∈ regular) : rename z = ⟨z, hz⟩ := by
      simp only [rename, dif_pos hz]
    have hname : ∀ z, decide (z ∉ regular) = false → (rename z : α) = z := by
      intro z hz
      have hr : z ∈ regular := by simpa using hz
      rw [hrename z hr]
    have hl : ∀ b ∈ blocks, ∀ t ∈ Ico b.1 (b.1 + b.2), decide (labelNat t ∉ regular) = false →
        ∃ c : ℝ, D.mkQ (formalDeparture labelNat coefficient t) = anchor (rename (labelNat t)) +
          c • D.mkQ (Pi.basisFun ℝ α (rename (labelNat t))) := by
      intro b hb t ht hr
      have hm : labelNat t ∈ regular := by simpa using hr
      simpa only [hrename _ hm] using hline b hb t ht hm
    obtain ⟨number, pathCode, hbound, hinj, hdecode⟩ := indexed_block_family_numbering D anchor
      (fun z : regular => (z : α)) rename labelNat coefficient (fun z => decide (z ∉ regular))
      blocks hind hname hl hnonzero hsize
    obtain ⟨code, _, hp⟩ := column_code_from_regular_forest hN hn label perfect regular number
      (fun z => number (rename z)) (fun z hz => congrArg number (hrename z hz))
      labelNat chunks blocks hentries hblocks pathCode hbound hinj hdecode hO hI
    exact ⟨code, hp⟩
  · have hno (z : α) : z ∉ regular := fun hz => hR ⟨z, hz⟩
    have hs := indexedRegularSegments_eq_nil labelNat (fun z => decide (z ∉ regular)) blocks
      (fun z => by simp [hno z])
    let number : regular → ℕ := fun z => False.elim (hno z z.property)
    let pathCode : ForestPathData.Code N
        (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length := by
      rw [hs]
      exact emptyForestPathCode N
    have hbound : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
        ∀ p ∈ segment, (0 : ℕ) < N := by simp only [hs, List.not_mem_nil, false_implies, implies_true]
    have hinj : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
        ∀ p ∈ segment,
        ∀ other ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
        ∀ q ∈ other, (0 : ℕ) = 0 → p.2 = q.2 := by
      simp only [hs, List.not_mem_nil, false_implies, implies_true]
    have hd : List.ofFn (fun i => evenEntries (decodeForestPaths pathCode i)) =
        (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).map
          (fun segment => segment.map (fun _ => (0 : ℕ))) := by
      have hl : (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length = 0 := by rw [hs]; rfl
      exact List.eq_nil_of_length_eq_zero (by simp only [List.length_ofFn, hl]) |>.trans (by rw [hs]; rfl)
    obtain ⟨code, _, hp⟩ := column_code_from_regular_forest hN hn label perfect regular number
      (fun _ => 0) (fun z hz => (hno z hz).elim)
      labelNat chunks blocks hentries hblocks pathCode hbound hinj hd hO hI
    exact ⟨code, hp⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LowRankColumnEncoding
namespace OAI

/-! Low-rank lit departures give a full code for the actual short-block column. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}


theorem imperfectColumnCount_le (perfect : Finset (Fin n)) :
    imperfectColumnCount perfect ≤ n := by
  exact (List.length_filter_le _ _).trans (by simp [columnPositionEntries])


/-- Only actual lit departures enter the low-rank premise. The short
blocks and their complete decoder are constructed, not supplied as data. -/
theorem low_rank_short_column_code (label : Fin n → α) (hn : 0 < n)
    (coefficient : ℕ → ℝ) (perfect : Finset (Fin n)) (s r : ℕ) (hs : 0 < s)
    (hno : ∀ S : Finset (EqualLabelPairs (fun i : perfect => label i.val)), S.card = r →
      ¬LinearIndependent ℝ (pairFamily (labelPairVectors (fun i : perfect => label i.val)
        (fun i => formalDeparture (columnNatLabel label hn) coefficient i.val.val)) S))
    (hgeometry : ShortColumnGeometry label hn coefficient perfect s) :
    ∃ omittedLabels blocks segments omittedRuns : ℕ,
      omittedLabels < 2 * r ∧
      blocks ≤ n / s + imperfectColumnCount perfect + 1 ∧
      segments ≤ (omittedLabels + 1) * blocks ∧
      omittedRuns ≤ omittedLabels * blocks ∧
      segments ≤ n ∧ omittedRuns ≤ n ∧
      ∃ code : ColumnDecoderCode (2 * n) segments omittedRuns (imperfectColumnCount perfect),
        decodeColumnPrefixPattern (show n ≤ 2 * n by omega) code =
          fun i j => decide (label i = label j) := by
  classical
  let labelNat := columnNatLabel label hn
  let chunks := shortColumnChunks label hn perfect s
  obtain ⟨blocks, hblocks, hsum, hcount, hvalid⟩ := shortColumnChunks_blocks label hn perfect s hs
  obtain ⟨D, regular, anchor, hsmall, hind, hline⟩ :=
    exists_regular_line_anchors (fun i : perfect => label i.val)
      (fun i => formalDeparture labelNat coefficient i.val.val) r hno
  have hl : ∀ b ∈ blocks, ∀ t ∈ Ico b.1 (b.1 + b.2), ∀ ht : labelNat t ∈ regular,
      ∃ c : ℝ, D.mkQ (formalDeparture labelNat coefficient t) =
        anchor ⟨labelNat t, ht⟩ + c • D.mkQ (Pi.basisFun ℝ α (labelNat t)) := by
    intro b hb t ht hr
    obtain ⟨htlo, hthi⟩ := mem_Ico.mp ht
    have htn : t < n := (mem_Ico.mp ht).2.trans_le (hvalid b hb).1
    have htp : columnNatPerfect perfect t = true := (hvalid b hb).2.2 t (by
      simp only [intervalPositions, List.mem_map, List.mem_range]
      exact ⟨t - b.1, by omega, by omega⟩)
    have hip : (⟨t, htn⟩ : Fin n) ∈ perfect := by
      simpa only [columnNatPerfect, dif_pos htn, decide_eq_true_eq] using htp
    exact hline ⟨labelNat t, hr⟩ ⟨⟨t, htn⟩, hip⟩ (by
      change label ⟨t, htn⟩ = columnNatLabel label hn t
      simp only [columnNatLabel, dif_pos htn])
  have hg (b) (hb : b ∈ blocks) := hgeometry b.1 b.2
    (hvalid b hb).1 (hvalid b hb).2.1 (hvalid b hb).2.2
  have hi : ∀ l, Sum.inl l ∈ chunks → ∀ i j k : Fin l.length,
      i ≤ j → j ≤ k → l.get i = l.get k → l.get j = l.get i := by
    intro l hl
    have hm : l ∈ chunks.filterMap (Sum.elim some (fun _ => none)) :=
      List.mem_filterMap.mpr ⟨.inl l, hl, rfl⟩
    rw [hblocks] at hm
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    exact (hg b hb).1
  have ho := columnChunk_piece_budgets chunks regularᶜ hi
  let pieces := columnChunkPieces (fun z => decide (z ∉ regular)) chunks
  let S := (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length
  let O := omittedPieceCount pieces
  have hp : (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).map
      (List.map Prod.snd) = pieces.filterMap (Sum.elim some (fun _ => none)) :=
    indexedRegularSegments_eq_regular_pieces labelNat _ chunks blocks hblocks
  have hS : S = regularPieceCount pieces := by
    have he := congrArg List.length hp
    simpa only [List.length_map, regularPieceCount] using he
  have hB : perfectChunkCount chunks = blocks.length := by
    change (chunks.filterMap (Sum.elim some (fun _ => none))).length = blocks.length
    change (shortColumnChunks label hn perfect s |>.filterMap (Sum.elim some (fun _ => none))).length = _
    rw [hblocks, List.length_map]
  have hO : O ≤ regularᶜ.card * blocks.length := by
    simpa only [pieces, mem_compl, hB] using ho.1
  have hSbound : S ≤ (regularᶜ.card + 1) * blocks.length := by
    rw [hS]
    simpa only [pieces, mem_compl, hB] using ho.2
  have hentries := shortColumnChunks_entries label hn perfect s
  have hpieces : pieces.length ≤ n := (columnChunkPieces_length_le _ chunks).trans (by
    rw [hentries]
    simp only [List.length_map, columnPositionEntries, List.length_ofFn]
    exact le_rfl)
  have hSn : S ≤ n := by
    rw [hS]
    exact (List.length_filterMap_le _ _).trans hpieces
  have hOn : O ≤ n := (List.length_filterMap_le _ _).trans hpieces
  obtain ⟨code, hcode⟩ := column_code_from_quotient_geometry (by omega : 0 < 2 * n)
    (by omega : n ≤ 2 * n) label perfect regular labelNat coefficient chunks blocks hentries hblocks
    D anchor hind hl (fun b hb => (hg b hb).2) (Nat.mul_le_mul_left 2 hsum) le_rfl le_rfl
  exact ⟨regularᶜ.card, blocks.length, S, O, hsmall, hcount, hSbound, hO, hSn, hOn, code, hcode⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LitBlockGeometry
namespace OAI

/-! Perfect blocks use only the lit divisibilities at their actual positions. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem positiveWord_iff_departures (h : ℕ) (x : ℤ) (w : List SignedStep) :
    PositiveWord h x w ↔ ∀ i : Fin w.length,
      (w.get i).divisor ∣ x + wordDisplacement h (w.take i.val) := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
      rw [positiveWord_cons, ih]
      constructor
      · rintro ⟨ha, hw⟩ i
        rcases i with ⟨i, hi⟩
        cases i with
        | zero => simpa using ha
        | succ i =>
            simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
              wordDisplacement_cons, add_assoc] using hw ⟨i, by simpa using hi⟩
      · intro hw
        refine ⟨?_, ?_⟩
        · simpa using hw ⟨0, by simp⟩
        · intro i
          simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
            wordDisplacement_cons, add_assoc] using hw ⟨i.val + 1, by simp⟩

theorem positiveWord_slice_of_lit {h : ℕ} {x : ℤ} {w : List SignedStep}
    (start len : ℕ) (hend : start + len ≤ w.length)
    (hlit : ∀ i : Fin w.length, start ≤ i.val → i.val < start + len →
      (w.get i).divisor ∣ x + wordDisplacement h (w.take i.val)) :
    PositiveWord h (x + wordDisplacement h (w.take start)) (wordSlice w start (start + len)) := by
  rw [positiveWord_iff_departures]
  intro i
  have hi : i.val < len := by
    have hl : (wordSlice w start (start + len)).length = len := by
      rw [wordSlice_length w (a := start) (b := start + len) (by omega) hend, Nat.add_sub_cancel_left]
    exact i.isLt.trans_eq hl
  have hp := hlit ⟨start + i.val, by omega⟩
    (show start ≤ start + i.val by omega) (show start + i.val < start + len by omega)
  have htake : (wordSlice w start (start + len)).take i.val = wordSlice w start (start + i.val) := by
    simp only [wordSlice, List.take_take, Nat.add_sub_cancel_left, Nat.min_eq_left hi.le]
  have he := congrArg (wordDisplacement h) (wordSlice_split w (show start ≤ start + i.val by omega))
  rw [wordDisplacement_append] at he
  change ((wordSlice w start (start + len))[i.val]).divisor ∣ _
  rw [htake]
  simpa only [List.get_eq_getElem, wordSlice, List.getElem_take, List.getElem_drop,
    ← he, add_assoc] using hp

theorem wordVertex_slice {h : ℕ} {x y : ℤ} {w : List SignedStep}
    (start len : ℕ)
    (hy : WordVertex h (x + wordDisplacement h (w.take start))
      (wordSlice w start (start + len)) y) : WordVertex h x w y := by
  obtain ⟨a, b, hab, hy⟩ := hy
  refine ⟨w.take start ++ a, b ++ w.drop (start + len), ?_, ?_⟩
  · calc
      w = w.take (start + len) ++ w.drop (start + len) := (List.take_append_drop _ _).symm
      _ = (w.take start ++ wordSlice w start (start + len)) ++ w.drop (start + len) := by
        rw [wordSlice_split w (by omega)]
      _ = (w.take start ++ a) ++ (b ++ w.drop (start + len)) := by
        rw [hab]
        simp only [List.append_assoc]
  · rw [wordDisplacement_append]
    simpa only [add_assoc] using hy

namespace ColumnWordPattern

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- Every numerical perfect block has the geometric properties used by
the universal code. Positivity is assumed only at the perfect positions;
unlit positions elsewhere in the trace impose no condition here. -/
theorem short_geometry_of_lit (w : ColumnWordPattern α) (hn : 0 < w.length)
    (value : α → ℕ) (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    {h s J : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (hh : 0 < h)
    (perfect : Finset (Fin w.length))
    (hlit : ∀ i ∈ perfect, (w.step value i.val).divisor ∣
      x + wordDisplacement h ((w.word value).take i.val))
    (heligible : ∀ a ∈ w.word value, supply a.tuple a.padding)
    (hq : ∀ a ∈ w.word value, 0 < a.padding)
    (hsq : ∀ a ∈ w.word value, Squarefree a.tuple)
    (hcard : ∀ a ∈ w.word value, a.tuple.primeFactors.card = J)
    (hchain : ∀ start len, start + len ≤ w.length → len ≤ s →
      (∀ t ∈ intervalPositions (start, len), columnNatPerfect perfect t = true) →
      (wordSlice (w.word value) start (start + len)).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (w.word value) p j →
      ¬p ∣ h ∧ ∀ a ∈ w.word value, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (w.word value) y → ¬ProhibitedSite h s supply y) :
    ShortColumnGeometry (fun i : Fin w.length => w.label i.val) hn
      (fun t => (w.coefficient h t : ℝ)) perfect s := by
  intro start len hend hlen hperfect
  have hlabel (t : ℕ) (ht : t < w.length) :
      columnNatLabel (fun i : Fin w.length => w.label i.val) hn t = w.label t := by
    simp only [columnNatLabel, dif_pos ht]
  have hpositive := positiveWord_slice_of_lit (h := h) (x := x) (w := w.word value)
    start len (by simpa using hend) (by
      intro i hlo hhi
      have hit : i.val < w.length := by simpa only [word_length] using i.isLt
      have hp := hperfect i.val (by
        simp only [intervalPositions, List.mem_map, List.mem_range]
        exact ⟨i.val - start, by omega, by omega⟩)
      have him : (⟨i.val, hit⟩ : Fin w.length) ∈ perfect := by
        simpa only [columnNatPerfect, dif_pos hit, decide_eq_true_eq] using hp
      change ((w.word value)[i.val]).divisor ∣ _
      simpa only [word, List.getElem_ofFn] using hlit ⟨i.val, hit⟩ him)
  have hg := w.block_geometry_of_slice value hvalue hprime hother start len hend hlen
    hpositive hh heligible hq hsq hcard (hchain start len hend hlen hperfect) hsupport
    (fun y hy => hsurvive y (wordVertex_slice start len hy))
  constructor
  · intro i j k hij hjk he
    have hi : i.val < len := by simpa only [blockLabelList, List.length_map, List.length_range] using i.isLt
    have hj : j.val < len := by simpa only [blockLabelList, List.length_map, List.length_range] using j.isLt
    have hk : k.val < len := by simpa only [blockLabelList, List.length_map, List.length_range] using k.isLt
    have hget (q : Fin (blockLabelList (columnNatLabel (fun i : Fin w.length => w.label i.val) hn) start len).length)
        (hq : q.val < len) :
        (blockLabelList (columnNatLabel (fun i : Fin w.length => w.label i.val) hn) start len).get q =
          w.label (start + q.val) := by
      change (blockLabelList (columnNatLabel (fun i : Fin w.length => w.label i.val) hn) start len)[q.val] = _
      simp only [blockLabelList, List.getElem_map, List.getElem_range]
      exact hlabel _ (by omega)
    rw [hget i hi, hget k hk] at he
    rw [hget j hj, hget i hi]
    exact hg.1 ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk he
  · intro a b z ha hab hb hc
    apply hg.2 a b z ha hab hb
    intro t ht
    rw [← hlabel t (by have := (mem_Ico.mp ht).2; omega)]
    exact hc t ht

end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LowRankColumnCover
namespace OAI

/-! Actual low-rank columns lie in one coefficient-independent finite universe. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem low_rank_column_in_budget_universe {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (label : Fin n → α) (hn : 0 < n)
    (coefficient : ℕ → ℝ) (perfect : Finset (Fin n)) (s r : ℕ) (hs : 0 < s)
    (L : ℝ) (hL : 1 ≤ L) (hnL : (n : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount perfect : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ S : Finset (EqualLabelPairs (fun i : perfect => label i.val)), S.card = r →
      ¬LinearIndependent ℝ (pairFamily (labelPairVectors (fun i : perfect => label i.val)
        (fun i => formalDeparture (columnNatLabel label hn) coefficient i.val.val)) S))
    (hgeometry : ShortColumnGeometry label hn coefficient perfect s) :
    ∃ code : BudgetColumnCode (2 * n) L,
      decodeBudgetColumnPattern (show n ≤ 2 * n by omega) code =
        fun i j => decide (label i = label j) := by
  obtain ⟨O, B, S, R, hO, hB, hS, hR, hSn, hRn, code, hcode⟩ :=
    low_rank_short_column_code label hn coefficient perfect s r hs hno hgeometry
  have hO' : (O : ℝ) ≤ 2 * L ^ (1 / 50 : ℝ) := by
    have : (O : ℝ) < 2 * r := by exact_mod_cast hO
    linarith
  have hbudget := column_budget_bound L hL n s (imperfectColumnCount perfect) O B S R
    hnL hsL hI hO' (by omega) hS hR
  obtain ⟨full, hfull⟩ := budget_column_code_of_counts (by omega : n ≤ 2 * n)
    (by omega : S ≤ 2 * n) (by omega : R ≤ 2 * n)
    ((imperfectColumnCount_le perfect).trans (by omega)) hbudget code
  exact ⟨full, hfull.trans hcode⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MidpointCut
namespace OAI

/-! Force the trace midpoint boundary by charging one extra imperfect position. -/

namespace TwoPointCorrelations

open _root_.Finset



/-- A block containing only retained perfect positions cannot cross the
erased midpoint. The erased step is still encoded by its ordinary
imperfect-position reference. -/
theorem perfect_block_avoids_cut {n : ℕ} (perfect : Finset (Fin n)) (cut : Fin n)
    (start len : ℕ) (_hend : start + len ≤ n)
    (hperfect : ∀ t ∈ intervalPositions (start, len),
      columnNatPerfect (perfect.erase cut) t = true) :
    start + len ≤ cut.val ∨ cut.val < start := by
  by_contra h
  have hlo : start ≤ cut.val := by omega
  have hhi : cut.val < start + len := by omega
  have hm : cut.val ∈ intervalPositions (start, len) := by
    simp only [intervalPositions, List.mem_map, List.mem_range]
    exact ⟨cut.val - start, by omega, by omega⟩
  have hp := hperfect cut.val hm
  simp [columnNatPerfect_fin] at hp

theorem isChain_slice_of_two_halves {α : Type*} {R : α → α → Prop}
    (w : List α) (cut start len : ℕ)
    (hleft : (w.take cut).IsChain R) (hright : (w.drop cut).IsChain R)
    (hside : start + len ≤ cut ∨ cut ≤ start) :
    ((w.drop start).take len).IsChain R := by
  rcases hside with hl | hr
  · have hs := (hleft.drop start).take len
    simpa only [List.drop_take, List.take_take, Nat.min_eq_left (by omega : len ≤ cut - start)] using hs
  · have hs := (hright.drop (start - cut)).take len
    simpa only [List.drop_drop, Nat.add_sub_cancel' hr] using hs

/-- The two actual nonbacktracking halves suffice for every retained
perfect block; no relation between the two midpoint tuples is needed. -/
theorem trace_perfect_block_chain {n : ℕ} (perfect : Finset (Fin n)) (cut : Fin n)
    (w : List SignedStep)
    (hleft : (w.take cut.val).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hright : (w.drop cut.val).IsChain (fun a b => a.tuple ≠ b.tuple))
    (start len : ℕ) (hend : start + len ≤ n)
    (hperfect : ∀ t ∈ intervalPositions (start, len),
      columnNatPerfect (perfect.erase cut) t = true) :
    (wordSlice w start (start + len)).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  have hs := perfect_block_avoids_cut perfect cut start len hend hperfect
  have hc := isChain_slice_of_two_halves w cut.val start len hleft hright
    (hs.imp_right Nat.le_of_lt)
  simpa only [wordSlice, Nat.add_sub_cancel_left] using hc


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NumericalColumnCover
namespace OAI

/-! A surviving numerical trace word belongs to the universal column code set. -/

namespace TwoPointCorrelations.ColumnWordPattern

open _root_.Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The complete column-covering implication. Only the two halves are
assumed nonbacktracking. All positivity premises are actual divisibilities
at the original perfect positions; one midpoint reference is charged to
the imperfect budget. The finite code universe is independent of `value`,
the signs, the padding, and the fixed other-column coefficients. -/
theorem numerical_column_in_universe (w : ColumnWordPattern α) (hn : 0 < w.length)
    (value : α → ℕ) (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    {h s J r : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (hh : 0 < h) (hs : 0 < s)
    (perfect : Finset (Fin w.length)) (cut : Fin w.length)
    (hlit : ∀ i ∈ perfect, (w.step value i.val).divisor ∣
      x + wordDisplacement h ((w.word value).take i.val))
    (heligible : ∀ a ∈ w.word value, supply a.tuple a.padding)
    (hq : ∀ a ∈ w.word value, 0 < a.padding)
    (hsq : ∀ a ∈ w.word value, Squarefree a.tuple)
    (hcard : ∀ a ∈ w.word value, a.tuple.primeFactors.card = J)
    (hleft : ((w.word value).take cut.val).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hright : ((w.word value).drop cut.val).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (w.word value) p j →
      ¬p ∣ h ∧ ∀ a ∈ w.word value, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (w.word value) y → ¬ProhibitedSite h s supply y)
    (L : ℝ) (hL : 1 ≤ L) (hnL : (w.length : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount (perfect.erase cut) : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ S : Finset (EqualLabelPairs
        (fun i : perfect.erase cut => w.label i.val.val)), S.card = r →
      ¬LinearIndependent ℝ (pairFamily (labelPairVectors
        (fun i : perfect.erase cut => w.label i.val.val)
        (fun i => formalDeparture (columnNatLabel (fun i : Fin w.length => w.label i.val) hn)
          (fun t => (w.coefficient h t : ℝ)) i.val.val)) S)) :
    ∃ code : BudgetColumnCode (2 * w.length) L,
      decodeBudgetColumnPattern (show w.length ≤ 2 * w.length by omega) code =
        fun i j => decide (w.label i.val = w.label j.val) := by
  have hg := w.short_geometry_of_lit hn value hvalue hprime hother hh (perfect.erase cut)
    (fun i hi => hlit i (mem_of_mem_erase hi)) heligible hq hsq hcard
    (fun start len hend _ hp => trace_perfect_block_chain perfect cut (w.word value)
      hleft hright start len hend hp) hsupport hsurvive
  exact low_rank_column_in_budget_universe (fun i : Fin w.length => w.label i.val) hn
    (fun t => (w.coefficient h t : ℝ)) (perfect.erase cut) s r hs L hL hnL hsL hrL hI hno hg

end TwoPointCorrelations.ColumnWordPattern

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding
namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations


attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]







@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleColumnWords
namespace OAI

/-! Each actual tuple word has the one-column resampling form used by the forest proof. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


private lemma cyclicIndex_val {R : ℕ} (hR : 0 < R) (t : Fin R) :
    cyclicIndex R hR t.val = t := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt t.isLt




lemma tupleColumnPattern_label {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (i : Fin R) :
    (tupleColumnPattern w hR forward padding j).label i.val = w j i := by
  simp only [tupleColumnPattern, cyclicIndex_val]

lemma columnTuple_split {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R) (j : Fin J) :
    (w j i).val * (∏ l ∈ univ.erase j, (w l i).val) = columnTuple w i := by
  exact mul_prod_erase univ (fun l => (w l i).val) (mem_univ j)

lemma tupleColumnPattern_step {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (i : Fin R) :
    (tupleColumnPattern w hR forward padding j).step Subtype.val i.val =
      ⟨forward i, columnTuple w i, padding i⟩ := by
  simp only [ColumnWordPattern.step, tupleColumnPattern, cyclicIndex_val, columnTuple_split]

lemma tupleColumnPattern_word {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) :
    (tupleColumnPattern w hR forward padding j).word Subtype.val =
      columnTupleWord w forward padding := by
  unfold ColumnWordPattern.word columnTupleWord
  congr 1
  funext i
  exact tupleColumnPattern_step w hR forward padding j i

/-- Disjoint column pools ensure the resampled prime cannot divide any
of the fixed other-column coefficients. -/
lemma tupleColumnPattern_not_dvd_other {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (hprime : ∀ l, ∀ p ∈ P l, p.Prime) (hdisjoint : ∀ l, l ≠ j → Disjoint (P j) (P l)) :
    ∀ p : P j, ∀ t < R,
      ¬p.val ∣ (tupleColumnPattern w hR forward padding j).otherColumns t := by
  intro p t _ hdiv
  have hp := hprime j p.val p.property
  change p.val ∣ ∏ l ∈ univ.erase j, (w l (cyclicIndex R hR t)).val at hdiv
  have hex := (hp.prime.dvd_finsetProd_iff (S := univ.erase j) (fun l => (w l (cyclicIndex R hR t)).val)).mp hdiv
  obtain ⟨l, hl, hpl⟩ := hex
  have hlne := (mem_erase.mp hl).1
  have hq : (w l (cyclicIndex R hR t)).val = p.val :=
    ((Nat.prime_dvd_prime_iff_eq hp (hprime l _ (w l _).property)).mp hpl).symm
  exact (disjoint_left.mp (hdisjoint l hlne)) p.property (hq ▸ (w l _).property)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleColumnCover
namespace OAI

/-! Apply the numerical forest cover simultaneously to all actual tuple columns. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


/-- A surviving lit numerical word supplies one member of the fixed joint
code universe. Its assumptions are the actual low-rank and arithmetic
conditions; no combinatorial covering assumption is made. -/
theorem tuple_column_array_cover_oai {J R : ℕ} (P : Fin J → Finset ℕ)
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    {h s r : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (hh : 0 < h) (hs : 0 < s)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hlit : ∀ i ∈ perfect, ((padding i : ℤ) * columnTuple w i) ∣
      x + wordDisplacement h ((columnTupleWord w forward padding).take i.val))
    (heligible : ∀ a ∈ columnTupleWord w forward padding, supply a.tuple a.padding)
    (hq : ∀ a ∈ columnTupleWord w forward padding, 0 < a.padding)
    (hsq : ∀ a ∈ columnTupleWord w forward padding, Squarefree a.tuple)
    (hcard : ∀ a ∈ columnTupleWord w forward padding, a.tuple.primeFactors.card = J)
    (hleft : ((columnTupleWord w forward padding).take cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hright : ((columnTupleWord w forward padding).drop cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (columnTupleWord w forward padding) p j →
      ¬p ∣ h ∧ ∀ a ∈ columnTupleWord w forward padding, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (columnTupleWord w forward padding) y →
      ¬ProhibitedSite h s supply y)
    (L : ℝ) (hL : 1 ≤ L) (hRL : (R : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount (perfect.erase cut) : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ j, ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r) :
    ∃ code : BudgetColumnArrayCode J (2 * R) L,
      ∀ j i l, decodeBudgetColumnArray (show R ≤ 2 * R by omega) code j i l =
        decide (w j i = w j l) := by
  have hcol : ∀ j, ∃ code : BudgetColumnCode (2 * R) L,
      decodeBudgetColumnPattern (show R ≤ 2 * R by omega) code =
        fun i l => decide (w j i = w j l) := by
    intro j
    let c := tupleColumnPattern w hR forward padding j
    have he : c.word Subtype.val = columnTupleWord w forward padding :=
      tupleColumnPattern_word w hR forward padding j
    have hv : Function.Injective (Subtype.val : P j → ℕ) := Subtype.val_injective
    have hp : ∀ p : P j, p.val.Prime := fun p => hprime j _ p.property
    have ho := tupleColumnPattern_not_dvd_other w hR forward padding j hprime (hdisjoint j)
    have ht : ∀ i ∈ perfect, (c.step Subtype.val i.val).divisor ∣
        x + wordDisplacement h ((c.word Subtype.val).take i.val) := by
      intro i hi
      rw [he, tupleColumnPattern_step]
      exact hlit i hi
    obtain ⟨code, hc⟩ := c.numerical_column_in_universe hR Subtype.val hv hp ho hh hs
      perfect cut ht (by simpa only [he] using heligible)
      (by simpa only [he] using hq) (by simpa only [he] using hsq)
      (by simpa only [he] using hcard) (by simpa only [he] using hleft)
      (by simpa only [he] using hright) (by simpa only [he] using hsupport)
      (by simpa only [he] using hsurvive) L hL hRL hsL hrL hI (hno j)
    refine ⟨code, hc.trans ?_⟩
    funext i l
    exact congrArg₂ (fun a b : P j => decide (a = b))
      (tupleColumnPattern_label w hR forward padding j i)
      (tupleColumnPattern_label w hR forward padding j l)
  obtain ⟨code, hc⟩ := budget_column_array_cover (show R ≤ 2 * R by omega)
    (fun j i l => decide (w j i = w j l)) hcol
  exact ⟨code, fun j i l => congrFun (congrFun (congrFun hc j) i) l⟩

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.tuple_column_array_cover_oai := @OAI.TwoPointCorrelations.tuple_column_array_cover_oai
