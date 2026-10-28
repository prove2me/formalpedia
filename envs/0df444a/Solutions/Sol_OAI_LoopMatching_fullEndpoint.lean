-- Prove2me | solution 1 for OAI.LoopMatching.fullEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:06:13.395138+00:00
-- url     : https://prove2.me/submissions/fd7f3d18-effe-4ad5-bf87-09e4e88ba57b

import Mathlib
import Definitions.Def_SingletonLoopMatching
import Definitions.Def_OAIW2LM004
import Theorems.Thm_OAI_BinaryMatching_Algorithm_R_partition_bracket

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_CountDecomposition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

open scoped BigOperators

namespace LoopMatching

theorem loopVertices_card_le {n : ℕ} (M : PartialMatching n) :
    (loopVertices M).card ≤ n := by
  classical
  simpa using Finset.card_le_card (Finset.subset_univ (loopVertices M))

theorem count_eq_sum_countWithLoops (G : Input) :
    count G = ∑ j ∈ Finset.range (G.n + 1), countWithLoops G j := by
  classical
  unfold count countWithLoops
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M hM
  symm
  calc
    _ = (if (loopVertices M).card = (loopVertices M).card then weight G M else 0) := by
      apply Finset.sum_eq_single (loopVertices M).card
      · intro j hj hne
        simp only [Ne.symm hne, ↓reduceIte]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr
          (Nat.lt_succ_of_le (loopVertices_card_le M)))).elim
    _ = weight G M := ite_eq_left rfl

theorem weight_eq_zero_of_loopMultiplicity_eq_zero (G : Input)
    (M : PartialMatching G.n) (v : Fin G.n)
    (hv : v ∈ loopVertices M) (hzero : loopMultiplicity G v = 0) :
    weight G M = 0 := by
  classical
  unfold weight
  rw [Finset.prod_eq_zero hv hzero, mul_zero]

theorem weight_eq_zero_of_multiplicity_eq_zero (G : Input)
    (M : PartialMatching G.n) (e : BinaryMatching.Pair G.n)
    (he : e ∈ M.val) (hzero : BinaryMatching.multiplicity G.ordinary e = 0) :
    weight G M = 0 := by
  classical
  unfold weight
  rw [Finset.prod_eq_zero he hzero, zero_mul]

theorem count_eq_zero_of_forall_weight_eq_zero (G : Input)
    (hzero : ∀ M : PartialMatching G.n, weight G M = 0) : count G = 0 := by
  classical
  unfold count
  exact Finset.sum_eq_zero (fun M _ => hzero M)

end LoopMatching

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_ExpandInput
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching

private lemma find_some_unique {α : Type*} (p : α → Bool) (xs : List α) (a : α)
    (ha : a ∈ xs) (hp : p a = true) (hu : ∀ b ∈ xs, p b = true → b=a) :
    xs.find? p = some a := by
  cases hf : xs.find? p with
  | none => exact False.elim ((List.find?_eq_none.mp hf a ha) hp)
  | some b =>
    have hb := hu b (List.mem_of_find?_eq_some hf) (List.find?_some hf)
    exact congrArg some hb

private lemma find_cross_block (n j i d : ℕ) (r : LoopRecord) (hd : d<j) :
    ((List.range j).map (crossRecord n r)).find?
      (fun e => e.left=i && e.right=n+d) =
      if r.vertex=i then some (crossRecord n r d) else none := by
  by_cases hi : r.vertex=i
  · rw [ite_eq_left hi]
    apply find_some_unique
    · exact List.mem_map.mpr ⟨d,List.mem_range.mpr hd,rfl⟩
    · simp [crossRecord,hi]
    · intro b hb hp
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      have he : n+c=n+d := by simpa [crossRecord,hi] using hp
      have : c=d := by omega
      subst c
      rfl
  · rw [ite_eq_right hi]
    apply List.find?_eq_none.mpr
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    simp [crossRecord,hi]

private lemma find_crossRecords (n j i d : ℕ) (rs : List LoopRecord) (hd : d<j) :
    (crossRecords n j rs).find? (fun e => e.left=i && e.right=n+d) =
      (rs.find? (fun r => r.vertex == i)).map (fun r => crossRecord n r d) := by
  induction rs with
  | nil => simp [crossRecords]
  | cons r rs ih =>
    change ((((List.range j).map (crossRecord n r)) ++ crossRecords n j rs).find?
      (fun e => e.left=i && e.right=n+d)) =
      ((r :: rs).find? (fun r => r.vertex == i)).map (fun r => crossRecord n r d)
    rw [List.find?_append, find_cross_block n j i d r hd]
    by_cases hi : r.vertex=i
    · simp [hi]
    · simp [hi, ih]

lemma multiplicity_expand_old (G : Input) (j : ℕ) (e : BinaryMatching.Pair G.n) :
    BinaryMatching.multiplicity (expand G j) (oldPair G j e) =
      BinaryMatching.multiplicity G.ordinary e := by
  have hn : (crossRecords G.n j G.loops).find?
      (fun r => r.left=e.val.1.val && r.right=e.val.2.val) = none := by
    apply List.find?_eq_none.mpr
    intro r hr
    obtain ⟨s,hs,d,hd,rfl⟩ := mem_crossRecords.mp hr
    have he := e.val.2.isLt
    have hne : G.n+d ≠ e.val.2.val := by omega
    simp [crossRecord,hne]
  change (match (G.ordinary.records ++ crossRecords G.n j G.loops).find?
      (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
      | none => 0 | some r => r.multiplicity) =
    (match G.ordinary.records.find?
      (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
      | none => 0 | some r => r.multiplicity)
  rw [List.find?_append, hn]
  cases G.ordinary.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) <;> rfl

lemma multiplicity_expand_cross (G : Input) (j : ℕ) (v : Fin G.n) (d : Fin j) :
    BinaryMatching.multiplicity (expand G j) (crossPair G j v d) = loopMultiplicity G v := by
  have hn : G.ordinary.records.find?
      (fun r => r.left=v.val && r.right=G.n+d.val) = none := by
    apply List.find?_eq_none.mpr
    intro r hr
    have hb := (G.ordinary.valid r hr).2
    change r.right < G.n at hb
    have hne : r.right ≠ G.n+d.val := by omega
    simp [hne]
  change (match (G.ordinary.records ++ crossRecords G.n j G.loops).find?
      (fun r => r.left=v.val && r.right=G.n+d.val) with
      | none => 0 | some r => r.multiplicity) = loopMultiplicity G v
  rw [List.find?_append, hn]
  change (match (crossRecords G.n j G.loops).find?
      (fun r => r.left=v.val && r.right=G.n+d.val) with
      | none => 0 | some r => r.multiplicity) = _
  rw [find_crossRecords G.n j v.val d.val G.loops d.isLt]
  unfold loopMultiplicity
  cases G.loops.find? (fun r => r.vertex == v.val) <;> rfl

lemma multiplicity_expand_dummy (G : Input) (j : ℕ) (e : BinaryMatching.Pair j) :
    BinaryMatching.multiplicity (expand G j) (dummyPair G j e) = 0 := by
  have hn : (expand G j).records.find?
      (fun r => r.left=G.n+e.val.1.val && r.right=G.n+e.val.2.val) = none := by
    apply List.find?_eq_none.mpr
    intro r hr
    have hb : r.left < G.n := by
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨hlt,hbound⟩ := G.ordinary.valid r hr
        change r.right < G.n at hbound
        omega
      · obtain ⟨s,hs,d,hd,rfl⟩ := mem_crossRecords.mp hr
        exact G.valid s hs
    have hne : r.left ≠ G.n+e.val.1.val := by omega
    simp [hne]
  change (match (expand G j).records.find?
      (fun r => r.left=G.n+e.val.1.val && r.right=G.n+e.val.2.val) with
      | none => 0 | some r => r.multiplicity) = 0
  rw [hn]

end LoopMatching

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_StackRoutine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Finset Polynomial

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : β → γ}

lemma machine_alphabets_finite (p : Routine ea eb f) (k : p.machine.tm.K) :
    Finite (p.machine.tm.Γ k) := by
  change Finite Bool
  infer_instance

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.StdSimplexCompat
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

variable [IsStrictOrderedRing R]

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

end Semiring

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Simplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Probability vectors on finite types, with their convexity and compactness properties.
The function-space simplex is the range of the weights of `Convexity.StdSimplex`.
-/

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

theorem probabilitySimplex_eq_range (Index : Type*) [Fintype Index] :
    probabilitySimplex Index =
      Set.range (fun simplex : Convexity.StdSimplex ℝ Index ↦ ⇑simplex.weights) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext weights
  simp [probabilitySimplex]

theorem convex_probabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro leftWeights leftMem rightWeights rightMem leftScale rightScale
    leftNonneg rightNonneg total
  constructor
  · intro index
    exact add_nonneg (mul_nonneg leftNonneg (leftMem.1 index))
      (mul_nonneg rightNonneg (rightMem.1 index))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, leftMem.2, rightMem.2, mul_one, total]

theorem single_mem_probabilitySimplex {Index : Type*} [Fintype Index]
    [DecidableEq Index] (index : Index) : Pi.single index 1 ∈ probabilitySimplex Index := by
  constructor
  · intro other
    simp only [Pi.single_apply]
    split <;> norm_num
  · simp

theorem isCompact_probabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (probabilitySimplex Index) := by
  rw [probabilitySimplex_eq_range]
  exact isCompact_range
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Index).continuous

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Coupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite pushforwards and couplings with a prescribed common marginal.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

theorem fiberMass_nonneg {A C : Type*} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (c : C) :
    0 ≤ fiberMass p f c := by
  apply Finset.sum_nonneg
  intro a _
  split <;> simp_all

theorem le_fiberMass_self {A C : Type*} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (a : A) :
    p a ≤ fiberMass p f (f a) := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b => if f b = f a then p b else 0)
    (by intro b _; split <;> simp_all) (Finset.mem_univ a)
  simpa only [fiberMass, ite_true] using h

theorem jointLaw_nonneg {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (z : A × B) : 0 ≤ jointLaw p q f g z := by
  unfold jointLaw
  split
  · exact div_nonneg (mul_nonneg (hp _) (hq _)) (fiberMass_nonneg hp f _)
  · rfl

theorem jointLaw_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (a : A) : (∑ b, jointLaw p q f g (a,b)) = p a := by
  have heq : ∀ b, jointLaw p q f g (a,b) =
      (p a / fiberMass p f (f a)) * (if g b=f a then q b else 0) := by
    intro b
    by_cases h : f a=g b
    · simp only [jointLaw, h, ite_true]
      ring
    · simp [jointLaw, h, Ne.symm h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change p a / fiberMass p f (f a) * fiberMass q g (f a) = p a
  rw [← hcompat]
  by_cases hz : fiberMass p f (f a) = 0
  · have ha : p a = 0 := le_antisymm (by simpa [hz] using le_fiberMass_self hp f a) (hp a)
    simp [ha]
  · exact div_mul_cancel₀ _ hz

theorem jointLaw_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (b : B) : (∑ a, jointLaw p q f g (a,b)) = q b := by
  have heq : ∀ a, jointLaw p q f g (a,b) =
      (q b / fiberMass q g (g b)) * (if f a=g b then p a else 0) := by
    intro a
    by_cases h : f a=g b
    · simp only [jointLaw, h, ite_true, ← hcompat]
      ring
    · simp [jointLaw, h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change q b / fiberMass q g (g b) * fiberMass p f (g b) = q b
  rw [hcompat]
  by_cases hz : fiberMass q g (g b) = 0
  · have hb : q b = 0 := le_antisymm (by simpa [hz] using le_fiberMass_self hq g b) (hq b)
    simp [hb]
  · exact div_mul_cancel₀ _ hz

theorem jointLaw_mem_simplex {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : p ∈ probabilitySimplex A) (hq : q ∈ probabilitySimplex B)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c) :
    jointLaw p q f g ∈ probabilitySimplex (A × B) := by
  refine ⟨jointLaw_nonneg hp.1 hq.1 f g, ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [jointLaw_first hp.1 f g hcompat]
  exact hp.2

theorem sum_subtype_supported {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P]
    (w : A → ℝ) (hsupp : ∀ a, ¬P a → w a = 0) :
    (∑ a : {a // P a}, w a.val) = ∑ a, w a := by
  have hh : (∑ a : {a // ¬P a}, w a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hsupp a.val a.property
  simpa only [hh, add_zero] using (Fintype.sum_subtype_add_sum_subtype P w)

/-- No mass is lost in retaining only compatible pairs. -/
theorem compatible_jointLaw_mem_simplex {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : p ∈ probabilitySimplex A) (hq : q ∈ probabilitySimplex B)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c) :
    (fun z : {z : A × B // f z.1=g z.2} => jointLaw p q f g z.val) ∈
      probabilitySimplex {z : A × B // f z.1=g z.2} := by
  refine ⟨fun z => jointLaw_nonneg hp.1 hq.1 f g z.val, ?_⟩
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2) (jointLaw p q f g)
    (by intro z hz; simp [jointLaw, hz])]
  exact (jointLaw_mem_simplex hp hq f g hcompat).2

theorem fiberMass_sum {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) : ∑ c, fiberMass p f c = ∑ a, p a := by
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

theorem fiberMass_expect {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (h : C → ℝ) :
    ∑ c, fiberMass p f c * h c = ∑ a, p a*h (f a) := by
  unfold fiberMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem fiberMass_mem_simplex {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (f : A → C) :
    fiberMass p f ∈ probabilitySimplex C :=
  ⟨fiberMass_nonneg hp.1 f, (fiberMass_sum p f).trans hp.2⟩

theorem jointLaw_expect_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : A → ℝ) : ∑ z : A × B, jointLaw p q f g z * h z.1 = ∑ a, p a*h a := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, jointLaw_first hp f g hcompat]

theorem jointLaw_expect_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : B → ℝ) : ∑ z : A × B, jointLaw p q f g z * h z.2 = ∑ b, q b*h b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, jointLaw_second hq f g hcompat]

theorem compatible_jointLaw_expect_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : A → ℝ) :
    ∑ z : {z : A × B // f z.1=g z.2}, jointLaw p q f g z.val * h z.val.1 = ∑ a, p a*h a := by
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2)
    (fun z => jointLaw p q f g z * h z.1)
    (by intro z hz; simp [jointLaw, hz])]
  exact jointLaw_expect_first hp f g hcompat h

theorem compatible_jointLaw_expect_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : B → ℝ) :
    ∑ z : {z : A × B // f z.1=g z.2}, jointLaw p q f g z.val * h z.val.2 = ∑ b, q b*h b := by
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2)
    (fun z => jointLaw p q f g z * h z.2)
    (by intro z hz; simp [jointLaw, hz])]
  exact jointLaw_expect_second hq f g hcompat h

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Basic
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite loopless multigraphs, perfect matching indicators, and their convex hull.
The edge type distinguishes parallel edges. Feasible laws are probability vectors
on perfect matchings with a prescribed mean.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem continuous_mean (G : LooplessGraph V E) : Continuous G.mean := by
  unfold mean
  fun_prop

omit [Fintype V] [DecidableEq V] in
theorem mean_mem_polytope (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) : G.mean p ∈ G.polytope := by
  have h := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun M _ ↦ hp.1 M) hp.2 (fun M _ ↦ subset_convexHull ℝ _ (Set.mem_range_self M))
  have he : G.mean p = ∑ M, p M • G.indicator M := by
    ext e
    simp [mean]
  rw [he]
  exact h

omit [Fintype V] [DecidableEq V] in
/-- Exact equivalence between the convex hull of matching indicators and feasible finite laws. -/
theorem mem_polytope_iff (G : LooplessGraph V E) (y : E → ℝ) :
    y ∈ G.polytope ↔ (G.feasibleLaws y).Nonempty := by
  classical
  constructor
  · intro hy
    have hc : Convex ℝ (G.mean '' probabilitySimplex G.Matching) :=
      (convex_probabilitySimplex G.Matching).linear_image G.meanLinear
    have hs : Set.range G.indicator ⊆ G.mean '' probabilitySimplex G.Matching := by
      rintro _ ⟨M, rfl⟩
      exact ⟨Pi.single M 1, single_mem_probabilitySimplex M, G.mean_single M⟩
    obtain ⟨p, hp, rfl⟩ := convexHull_min hs hc hy
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact G.mean_mem_polytope hp

omit [Fintype V] [DecidableEq V] in
theorem compact_polytope (G : LooplessGraph V E) : IsCompact G.polytope := by
  have heq : G.polytope = G.mean '' probabilitySimplex G.Matching := by
    ext y
    rw [G.mem_polytope_iff]
    rfl
  rw [heq]
  exact (isCompact_probabilitySimplex G.Matching).image G.continuous_mean


end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_OddCuts
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Degree and odd-cut constraints for the perfect matching polytope.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] in
theorem degree_indicator (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    G.degree (G.indicator M) v = 1 := by
  obtain ⟨e, ⟨he, hev⟩, huniq⟩ := M.property v
  rw [degree, Finset.sum_eq_single e]
  · simp [hev, indicator, he]
  · intro e' _ hne
    by_cases hv : G.Incident v e'
    · have hh : e' ∉ M.val := by
        intro hm
        exact hne (huniq e' ⟨hm, hv⟩)
      simp [hv, indicator, hh]
    · simp [hv]
  · simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem incidence_sum (G : LooplessGraph V E) (e : E) (S : Finset V) :
    (∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0) =
      (if G.left e ∈ S then 1 else 0) + (if G.right e ∈ S then 1 else 0) := by
  have hv : ∀ v, (if G.Incident v e then (1:ℕ) else 0) =
      (if v = G.left e then 1 else 0) + (if v = G.right e then 1 else 0) := by
    intro v
    by_cases hl : v = G.left e <;> by_cases hr : v = G.right e
    · exact ((G.loopless e) (hl.symm.trans hr)).elim
    · simp [Incident, hl, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, hr, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, Ne.symm hl, Ne.symm hr, hl, hr]
  simp_rw [hv, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incidence_count (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) :
    (∑ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0))) = S.card := by
  have hsum : ∀ v, (∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0) = 1 := by
    intro v
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [hev]
    · intro e' he' hh
      have hv : ¬G.Incident v e' := fun hv => hh (hu e' ⟨he', hv⟩)
      simp [hv]
    · simp [he]
  calc
    _ = ∑ e ∈ M.val, ∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0 := by
      simp_rw [incidence_sum]
    _ = ∑ v ∈ S, ∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0 := Finset.sum_comm
    _ = S.card := by simp_rw [hsum]; simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_crosses_odd (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) (hS : Odd S.card) : ∃ e ∈ M.val, G.Crosses S e := by
  by_contra h
  push Not at h
  have heq : ∀ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0)) = 2*(if G.left e ∈ S then 1 else 0) := by
    intro e he
    have hc := h e he
    simp only [Crosses] at hc
    by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
      simp_all
  have hh := G.matching_incidence_count M S
  have heqsum := Finset.sum_congr rfl heq
  rw [heqsum, ← Finset.mul_sum] at hh
  obtain ⟨k, hk⟩ := hS
  omega


omit [Fintype V] [DecidableEq E] in
theorem convex_constraintPolytope (G : LooplessGraph V E) :
    Convex ℝ G.constraintPolytope := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_, ?_⟩
  · intro v
    rw [degree_linear, hx.2.1, hy.2.1, mul_one, mul_one, hab]
  · intro S hS
    rw [cutMass_linear]
    calc
      1 = a*1+b*1 := by linarith
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 S hS) ha)
        (mul_le_mul_of_nonneg_left (hy.2.2 S hS) hb)

omit [Fintype V] in
theorem indicator_mem_constraintPolytope (G : LooplessGraph V E) (M : G.Matching) :
    G.indicator M ∈ G.constraintPolytope := by
  refine ⟨?_, G.degree_indicator M, ?_⟩
  · intro e; simp [indicator]; split <;> norm_num
  · intro S hS
    obtain ⟨e, he, hc⟩ := G.matching_crosses_odd M S hS
    have h := Finset.single_le_sum (f := G.indicator M)
      (s := G.cut S) (a := e) (by intro e' _; simp [indicator]; split <;> norm_num)
      ((G.mem_cut S e).mpr hc)
    simpa only [cutMass, indicator, he, ite_true] using h

omit [Fintype V] in
theorem polytope_subset_constraintPolytope (G : LooplessGraph V E) :
    G.polytope ⊆ G.constraintPolytope := by
  apply convexHull_min
  · rintro x ⟨M, rfl⟩
    exact G.indicator_mem_constraintPolytope M
  · exact G.convex_constraintPolytope

omit [Fintype V] [DecidableEq E] in
theorem constraint_coordinate_le_one (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (e : E) : x e ≤ 1 := by
  have h := Finset.single_le_sum (f := fun e' => if G.Incident (G.left e) e' then x e' else 0)
    (s := Finset.univ) (a := e) (by
      intro e' _; split; exact hx.1 e'; rfl) (Finset.mem_univ e)
  have he : G.Incident (G.left e) e := Or.inl rfl
  change (if G.Incident (G.left e) e then x e else 0) ≤ G.degree x (G.left e) at h
  simpa only [he, ite_true, hx.2.1] using h

omit [Fintype V] [DecidableEq E] in
theorem continuous_degree (G : LooplessGraph V E) (v : V) :
    Continuous (fun x : E → ℝ => G.degree x v) := by
  unfold degree
  apply continuous_finsetSum
  intro e _
  split <;> fun_prop

omit [Fintype V] [DecidableEq E] in
theorem continuous_cutMass (G : LooplessGraph V E) (S : Finset V) :
    Continuous (fun x : E → ℝ => G.cutMass x S) := by
  unfold cutMass
  fun_prop

omit [Fintype V] [DecidableEq E] in
theorem isClosed_constraintPolytope (G : LooplessGraph V E) :
    IsClosed G.constraintPolytope := by
  simp only [constraintPolytope, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)).inter
    ((isClosed_iInter fun v => isClosed_eq (G.continuous_degree v) continuous_const).inter
      (isClosed_iInter fun S => isClosed_iInter fun _ =>
        isClosed_le continuous_const (G.continuous_cutMass S)))

omit [Fintype V] [DecidableEq E] in
theorem isCompact_constraintPolytope (G : LooplessGraph V E) :
    IsCompact G.constraintPolytope := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : E → ℝ) 1)).of_isClosed_subset
    G.isClosed_constraintPolytope
  intro x hx
  exact ⟨hx.1, fun e => G.constraint_coordinate_le_one hx e⟩

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Contraction
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Contraction of tight odd cuts and gluing of perfect matchings and their laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_crosses (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.Crosses S (G.boundaryEdge S M).val :=
  (G.onSide_incident_none S _).mp (Classical.choose_spec (M.property none)).1.2

omit [Fintype E] in
theorem indicator_glue_left (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide S).indicator z.val.1 e := by
  simp only [indicator, glueMatching, G.mem_glued_left S z.val.1 z.val.2 z.property e]

omit [Fintype E] in
theorem indicator_glue_right (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide Sᶜ).indicator z.val.2 e := by
  simp only [indicator, glueMatching, G.mem_glued_right S z.val.1 z.val.2 z.property e]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundary_eq_iff_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) : (G.boundaryEdge S M).val=e.val ↔ e ∈ M.val := by
  constructor
  · intro h
    have he : G.boundaryEdge S M = e := Subtype.ext h
    exact he ▸ G.boundaryEdge_mem S M
  · intro h
    exact (congrArg Subtype.val (G.eq_boundaryEdge S M h hc)).symm

omit [Fintype V] in
theorem boundary_fiber (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e.val = (G.onSide S).mean p e := by
  unfold fiberMass mean
  apply Finset.sum_congr rfl
  intro M _
  simp only [G.boundary_eq_iff_mem S M e hc, indicator]
  split <;> simp

omit [Fintype V] in
theorem boundary_fiber_zero (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : E) (hc : ¬G.Crosses S e) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e = 0 := by
  apply Finset.sum_eq_zero
  intro M _
  have he : (G.boundaryEdge S M).val ≠ e := by
    intro h
    exact hc (h ▸ G.boundaryEdge_crosses S M)
  simp [he]

/-- Exact coupling across a cut, for multigraphs with distinct edge identities. -/
theorem couple_laws (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ)
    {p : (G.onSide S).Matching → ℝ} {q : (G.onSide Sᶜ).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (G.onSide S).Matching)
    (hq : q ∈ probabilitySimplex (G.onSide Sᶜ).Matching)
    (hpx : ∀ e, (G.onSide S).mean p e = x e.val)
    (hqx : ∀ e, (G.onSide Sᶜ).mean q e = x e.val) :
    ∃ r, r ∈ G.feasibleLaws x := by
  let f := fun M : (G.onSide S).Matching => (G.boundaryEdge S M).val
  let g := fun M : (G.onSide Sᶜ).Matching => (G.boundaryEdge Sᶜ M).val
  have hc : ∀ e, fiberMass p f e = fiberMass q g e := by
    intro e
    by_cases he : G.Crosses S e
    · have hk : G.left e ∈ S ∨ G.right e ∈ S := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      have he' := (G.crosses_compl S e).mpr he
      have hk' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := he'.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      rw [G.boundary_fiber S p ⟨e,hk⟩ he, G.boundary_fiber Sᶜ q ⟨e,hk'⟩ he', hpx, hqx]
    · have he' : ¬G.Crosses Sᶜ e := fun h => he ((G.crosses_compl S e).mp h)
      rw [G.boundary_fiber_zero S p e he, G.boundary_fiber_zero Sᶜ q e he']
  let Z := {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching // f z.1=g z.2}
  let w : Z → ℝ := fun z => jointLaw p q f g z.val
  have hw : w ∈ probabilitySimplex Z := compatible_jointLaw_mem_simplex hp hq f g hc
  refine ⟨fiberMass w (G.glueMatching S), fiberMass_mem_simplex hw _, ?_⟩
  ext e
  rw [mean, fiberMass_expect]
  by_cases he : G.left e ∈ S ∨ G.right e ∈ S
  · have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide S).indicator z.val.1 ⟨e,he⟩ := fun z => G.indicator_glue_left S z ⟨e,he⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_first hp.1 f g hc
      (fun M => (G.onSide S).indicator M ⟨e,he⟩)).trans (hpx ⟨e,he⟩)
  · have he' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := by
      simp only [not_or] at he
      exact Or.inl (Finset.mem_compl.mpr he.1)
    have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide Sᶜ).indicator z.val.2 ⟨e,he'⟩ := fun z => G.indicator_glue_right S z ⟨e,he'⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_second hq.1 f g hc
      (fun M => (G.onSide Sᶜ).indicator M ⟨e,he'⟩)).trans (hqx ⟨e,he'⟩)

theorem liftVertices_card (S : Finset V) (T : Finset (Option {v // v ∈ S}))
    (hn : none ∉ T) : (liftVertices S T).card = T.card := by
  apply Finset.card_bij (fun v _ => sideMap S v)
  · intro v hv
    exact (mem_liftVertices S T v).mp hv
  · intro v hv w hw he
    have hvS : v ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T v).mp hv
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    have hwS : w ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T w).mp hw
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    simp only [sideMap, hvS, hwS, ↓reduceDIte, Option.some.injEq] at he
    exact congrArg Subtype.val he
  · intro t ht
    cases t with
    | none => exact (hn ht).elim
    | some v => exact ⟨v.val, by simpa only [mem_liftVertices, sideMap_some] using ht, sideMap_some S v⟩

omit [Fintype E] [DecidableEq E] in
theorem onSide_cut_crosses (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Crosses T e ↔ G.Crosses (liftVertices S T) e.val := by
  simp only [Crosses, mem_liftVertices]
  rfl

omit [Fintype E] [DecidableEq E] in
theorem crosses_lift_kept (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : E)
    (he : G.Crosses (liftVertices S T) e) : G.left e ∈ S ∨ G.right e ∈ S := by
  by_contra h
  simp only [not_or] at h
  simp only [Crosses, mem_liftVertices, sideMap, h.1, h.2, ↓reduceDIte] at he
  tauto

omit [DecidableEq E] in
theorem onSide_cutMass (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (T : Finset (Option {v // v ∈ S})) :
    (G.onSide S).cutMass (fun e => x e.val) T = G.cutMass x (liftVertices S T) := by
  simp only [cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_cut_crosses S T]
  exact sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses (liftVertices S T) e then x e else 0)
    (by intro e he; rw [ite_eq_right (fun hc => he (G.crosses_lift_kept S T e hc))])

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_some (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (v : {v // v ∈ S}) :
    (G.onSide S).degree (fun e => x e.val) (some v) = G.degree x v.val := by
  simp only [degree]
  simp_rw [G.onSide_incident_some S v]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Incident v.val e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl (h.symm ▸ v.property))
  · exact he (Or.inr (h.symm ▸ v.property))

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_none (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ) :
    (G.onSide S).degree (fun e => x e.val) none = G.cutMass x S := by
  simp only [degree, cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_incident_none S]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses S e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl h.1)
  · exact he (Or.inr h.2)

theorem odd_compl_of_even {W : Type*} [Fintype W] [DecidableEq W]
    (hn : Even (Fintype.card W)) {T : Finset W} (hT : Odd T.card) : Odd Tᶜ.card := by
  rcases hn with ⟨k,hk⟩
  rcases hT with ⟨l,hl⟩
  have hle := Finset.card_le_univ T
  rw [Finset.card_compl]
  refine ⟨k-l-1, ?_⟩
  omega

omit [DecidableEq E] in
/-- Exact inheritance of the odd-cut system under contraction of a tight odd cut. -/
theorem restriction_mem_constraints (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (S : Finset V) (hS : Odd S.card)
    (htight : G.cutMass x S = 1) :
    (fun e : {e // G.left e ∈ S ∨ G.right e ∈ S} => x e.val) ∈
      (G.onSide S).constraintPolytope := by
  refine ⟨fun e => hx.1 e.val, ?_, ?_⟩
  · intro v
    cases v with
    | none => exact (G.onSide_degree_none S x).trans htight
    | some v => exact (G.onSide_degree_some S x v).trans (hx.2.1 v.val)
  · intro T hT
    by_cases hn : none ∈ T
    · have hn' : none ∉ Tᶜ := by simpa using hn
      have hnEven : Even (Fintype.card (Option {v // v ∈ S})) := by
        simp only [Fintype.card_option, Fintype.card_coe]
        exact hS.add_odd odd_one
      have hTc := odd_compl_of_even hnEven hT
      have hh := hx.2.2 (liftVertices S Tᶜ) (by rwa [liftVertices_card S Tᶜ hn'])
      rw [← G.onSide_cutMass S x Tᶜ] at hh
      simpa only [cutMass, cut_compl] using hh
    · rw [G.onSide_cutMass S x T]
      exact hx.2.2 _ (by rwa [liftVertices_card S T hn])

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Polyhedron
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite polyhedra, local perturbations, and quotient dimension bounds.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

section PolyhedralPrelude
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype J] in
theorem extreme_point_direction_zero (P : Set (J → ℝ)) {x : J → ℝ}
    (hx : x ∈ Set.extremePoints ℝ P) (u : J → ℝ)
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ P) : u=0 := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • u ∈ P := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0:ℝ))
    exact hc.eventually hu
  -- choose a strictly positive point using the right-hand punctured neighborhood
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x+t • u ∈ P ∧ x+(-t) • u ∈ P) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  have hseg : x ∈ openSegment ℝ (x+a • u) (x+(-a) • u) := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he := (mem_extremePoints.mp hx).2 _ ha _ hna hseg |>.1
  ext j
  have hj := congrFun he j
  change x j+a*u j=x j at hj
  change u j=0
  exact (mul_eq_zero.mp (by linarith : a*u j=0)).resolve_left (ne_of_gt ha0)


end PolyhedralPrelude

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Polytope
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Tutte's criterion and Edmonds' perfect matching polytope theorem for multigraphs.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem supportSimple_edge (G : LooplessGraph V E) {x : E → ℝ} {e : E} (he : 0 < x e) :
    (G.supportSimple x).Adj (G.left e) (G.right e) := ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem sum_pred_le_one {C : Type*} [Fintype C] (P : C → Prop) [DecidablePred P]
    (huniq : ∀ a b, P a → P b → a=b) : (∑ c, if P c then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ a, P a
  · obtain ⟨a,ha⟩ := h
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      rw [ite_eq_right]
      intro hPb
      exact hb (huniq b a hPb ha)
    · simp
  · simp only [not_exists] at h
    simp [h]

omit [Fintype V] [DecidableEq E] in
/-- The weighted cut-counting argument in Tutte's criterion. -/
theorem odd_family_bound (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {C : Type*} [Fintype C] [DecidableEq C]
    (U : Finset V) (T : C → Finset V)
    (hodd : ∀ c, Odd (T c).card)
    (hdisj : ∀ c v, v ∈ T c → v ∉ U)
    (huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b)
    (hclosed : ∀ e, 0 < x e → G.left e ∉ U → G.right e ∉ U →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c) :
    Fintype.card C ≤ U.card := by
  have hcuts : (Fintype.card C : ℝ) ≤ ∑ c, G.cutMass x (T c) := by
    calc
      _ = ∑ c : C, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ => hx.2.2 (T c) (hodd c)
  have hedges : ∀ e, (∑ c, if G.Crosses (T c) e then x e else 0) ≤
      (if G.left e ∈ U then x e else 0) + (if G.right e ∈ U then x e else 0) := by
    intro e
    by_cases hz : x e=0
    · simp [hz]
    have hp : 0 < x e := lt_of_le_of_ne (hx.1 e) (Ne.symm hz)
    by_cases hl : G.left e ∈ U <;> by_cases hr : G.right e ∈ U
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        rcases hc with h | h
        · exact hdisj c _ h.1 hl
        · exact hdisj c _ h.2 hr
      simp [hzero, hl, hr, hx.1 e]
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.right e ∈ T c := by
        intro c
        have hn : G.left e ∉ T c := fun h => hdisj c _ h hl
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.right e ∈ T c)
        (fun a b => huniq a b (G.right e))
      have heq' : (∑ c, if G.right e ∈ T c then x e else 0) =
          (∑ c, if G.right e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.left e ∈ T c := by
        intro c
        have hn : G.right e ∉ T c := fun h => hdisj c _ h hr
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.left e ∈ T c)
        (fun a b => huniq a b (G.left e))
      have heq' : (∑ c, if G.left e ∈ T c then x e else 0) =
          (∑ c, if G.left e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        have hiff := hclosed e hp hl hr c
        unfold Crosses at hc
        tauto
      simp [hzero, hl, hr]
  have hdegree : ∑ v ∈ U, G.degree x v = (U.card : ℝ) := by
    simp_rw [hx.2.1]
    simp
  have hsum : (∑ e : E, ((if G.left e ∈ U then x e else 0) +
      (if G.right e ∈ U then x e else 0))) = ∑ v ∈ U, G.degree x v := by
    simp only [degree]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have hf : ∀ v, (if G.Incident v e then x e else 0) =
        (if G.left e = v then x e else 0) + (if G.right e = v then x e else 0) := by
      intro v
      by_cases hl : G.left e=v <;> by_cases hr : G.right e=v
      · exact (G.loopless e (hl.trans hr.symm)).elim
      all_goals simp [Incident, hl, hr]
    simp_rw [hf]
    rw [Finset.sum_add_distrib]
    simp
  have hbound := (Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hedges e))
  rw [hsum, hdegree] at hbound
  have hcutEq : (∑ c, G.cutMass x (T c)) = ∑ e, ∑ c, if G.Crosses (T c) e then x e else 0 := by
    simp only [cutMass, cut, Finset.sum_filter]
    exact Finset.sum_comm
  exact_mod_cast hcuts.trans (hcutEq ▸ hbound)


omit [DecidableEq E] in
theorem supportSimple_has_perfectMatching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : (G.supportSimple x).Subgraph, M.IsPerfectMatching := by
  classical
  apply SimpleGraph.tutte.mpr
  intro U
  let H := (⊤ : (G.supportSimple x).Subgraph).deleteVerts U
  let C := H.coe.oddComponents
  let : Fintype C := Fintype.ofFinite C
  let T : C → Finset V := fun c => (Subtype.val '' c.val.supp).toFinset
  have hnot : ∀ v : H.verts, v.val ∉ U := by
    intro v
    have hv := v.property
    simpa [H] using hv
  have hT : ∀ c : C, ∀ v : V, v ∈ T c ↔ ∃ w : H.verts, w ∈ c.val.supp ∧ w.val=v := by
    intro c v
    simp [T]
  have hodd : ∀ c : C, Odd (T c).card := by
    intro c
    have hc := c.property
    change Odd c.val.supp.ncard at hc
    change Odd ((Subtype.val '' c.val.supp).toFinset.card)
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hc
  have hdisj : ∀ c v, v ∈ T c → v ∉ U.toFinset := by
    intro c v hv
    obtain ⟨w,_,rfl⟩ := (hT c v).mp hv
    simpa using hnot w
  have huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b := by
    intro a b v ha hb
    obtain ⟨wa,hwa,rfl⟩ := (hT a v).mp ha
    obtain ⟨wb,hwb,he⟩ := (hT b wa.val).mp hb
    have hw : wb=wa := Subtype.ext he
    subst wb
    exact Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex hwa hwb)
  have hclosed : ∀ e, 0<x e → G.left e ∉ U.toFinset → G.right e ∉ U.toFinset →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c := by
    intro e he hl hr c
    have hl' : G.left e ∈ H.verts := by simpa [H] using hl
    have hr' : G.right e ∈ H.verts := by simpa [H] using hr
    have ha : H.Adj (G.left e) (G.right e) := by
      simpa [H, SimpleGraph.Subgraph.deleteVerts_adj] using
        And.intro hl (And.intro hr (G.supportSimple_edge he))
    change G.left e ∈ (Subtype.val '' c.val.supp).toFinset ↔
      G.right e ∈ (Subtype.val '' c.val.supp).toFinset
    simp only [Set.mem_toFinset]
    exact ⟨fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hr' ha,
      fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hl' ha.symm⟩
  have hb := G.odd_family_bound hx U.toFinset T hodd hdisj huniq hclosed
  change ¬ U.ncard < H.coe.oddComponents.ncard
  have hcard : Fintype.card C = H.coe.oddComponents.ncard := by
    simp [C, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hcard] at hb
  exact not_lt_of_ge (by simpa only [← Set.ncard_eq_toFinset_card'] using hb)


theorem exists_supported_matching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : G.Matching, ∀ e ∈ M.val, 0 < x e := by
  classical
  obtain ⟨M,hM⟩ := G.supportSimple_has_perfectMatching hx
  have he : ∀ q ∈ M.edgeSet, ∃ e, 0<x e ∧ s(G.left e,G.right e)=q := by
    intro q
    induction q using Sym2.inductionOn with
    | hf v w =>
      intro hq
      obtain ⟨e,he,hor⟩ := (SimpleGraph.Subgraph.mem_edgeSet.mp hq).adj_sub
      refine ⟨e,he,Sym2.eq_iff.mpr hor⟩
  let f : M.edgeSet → E := fun q => (he q.val q.property).choose
  have hf : ∀ q, 0<x (f q) ∧ s(G.left (f q),G.right (f q))=q.val :=
    fun q => (he q.val q.property).choose_spec
  let F : Finset E := Finset.univ.image f
  have hF : G.IsPerfectMatching F := by
    intro v
    obtain ⟨w,hw,hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
    let q : M.edgeSet := ⟨s(v,w),SimpleGraph.Subgraph.mem_edgeSet.mpr hw⟩
    refine ⟨f q,⟨Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩,?_⟩
    · rcases Sym2.eq_iff.mp (hf q).2 with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    · intro e he'
      obtain ⟨q',_,rfl⟩ := Finset.mem_image.mp he'.1
      have hq : q'=q := by
        apply Subtype.ext
        rcases he'.2 with hl | hr
        · have hval : q'.val=s(v,G.right (f q')) := by rw [← (hf q').2, hl]
          have hAdj : M.Adj v (G.right (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
        · have hval : q'.val=s(v,G.left (f q')) := by
            rw [← (hf q').2, hr, Sym2.eq_swap]
          have hAdj : M.Adj v (G.left (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
      exact congrArg f hq
  refine ⟨⟨F,hF⟩,?_⟩
  intro e he'
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp he'
  exact (hf q).1


omit [DecidableEq E] in
/-- Local two-sided perturbations for the degree and odd-cut constraint system. -/
theorem constraint_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (u : E → ℝ)
    (hzero : ∀ e, x e=0 → u e=0) (hdeg : ∀ v, G.degree u v=0)
    (hcut : ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ G.constraintPolytope := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, ∀ e, 0≤(x+t • u) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · exact Filter.Eventually.of_forall (by intro t; simp [he,hzero e he])
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun t : ℝ => (x+t • u) e) := by fun_prop
      have hh : ∀ᶠ t : ℝ in 𝓝 0, 0<(x+t • u) e := (isOpen_lt continuous_const hc).mem_nhds
        (by simpa using hp : 0<(x+(0:ℝ) • u) e)
      exact hh.mono fun t ht => ht.le
  have hodd : ∀ᶠ t : ℝ in 𝓝 0, ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t • u) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases ht : G.cutMass x S=1
      · exact Filter.Eventually.of_forall (by
          intro t _
          have he := G.cutMass_linear x u 1 t S
          simp only [one_smul, one_mul, hcut S hS ht, mul_zero, add_zero, ht] at he
          exact he.ge)
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm ht)
        have hc : Continuous (fun t : ℝ => G.cutMass (x+t • u) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ t : ℝ in 𝓝 0, 1<G.cutMass (x+t • u) S := (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using hp : 1<G.cutMass (x+(0:ℝ) • u) S)
        exact hh.mono fun t ht _ => ht.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd] with t hn hodd
  refine ⟨hn,?_,hodd⟩
  intro v
  have he := G.degree_linear x u 1 t v
  simpa only [one_smul, one_mul, hdeg, mul_zero, add_zero, hx.2.1] using he

omit [Fintype V] [DecidableEq E] in
 theorem degree_sub (G : LooplessGraph V E) (x y : E → ℝ) (v : V) :
    G.degree (x-y) v = G.degree x v-G.degree y v := by
  have h := G.degree_linear x y 1 (-1) v
  simpa [sub_eq_add_neg] using h

omit [DecidableEq E] in
/-- Without a nontrivial tight odd cut, only degrees constrain a supported direction. -/
theorem trivial_tight_cut_preserved (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1)
    (u : E → ℝ) (hdeg : ∀ v, G.degree u v=0) :
    ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0 := by
  intro S hS ht
  have hc := odd_compl_of_even heven hS
  have hsmall : S.card=1 ∨ Sᶜ.card=1 := by
    have hn : ¬ (3≤S.card ∧ 3≤Sᶜ.card) := fun h => hnt ⟨S,hS,h.1,h.2,ht⟩
    rcases hS with ⟨k,hk⟩
    rcases hc with ⟨l,hl⟩
    omega
  rcases hsmall with hs | hs
  · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hs
    simpa using hdeg v
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hs
    have hh : G.cutMass u Sᶜ=0 := by rw [hv,cutMass_singleton,hdeg]
    simpa only [cutMass,cut_compl] using hh

 theorem extreme_no_tight_integral (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ Set.extremePoints ℝ G.constraintPolytope)
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    ∃ M : G.Matching, G.indicator M=x := by
  have hxQ := (mem_extremePoints.mp hx).1
  obtain ⟨M,hM⟩ := G.exists_supported_matching hxQ
  have hd : ∀ v, G.degree (G.indicator M-x) v=0 := by
    intro v
    rw [degree_sub,degree_indicator,hxQ.2.1,sub_self]
  have hz : ∀ e, x e=0 → (G.indicator M-x) e=0 := by
    intro e he
    have hn : e ∉ M.val := fun h => (hM e h).ne' he
    simp [indicator,hn,he]
  have hu := G.constraint_eventually_line hxQ (G.indicator M-x) hz hd
    (G.trivial_tight_cut_preserved heven hnt _ hd)
  have he := extreme_point_direction_zero G.constraintPolytope hx _ hu
  exact ⟨M,sub_eq_zero.mp he⟩


/-- Induction over even orders, using only proved cut coupling and Mathlib Tutte. -/
theorem constraint_subset_polytope_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n →
      G.constraintPolytope ⊆ G.polytope := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    have hex : Set.extremePoints ℝ G.constraintPolytope ⊆ G.polytope := by
      intro x hx
      have hxQ := (mem_extremePoints.mp hx).1
      by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
      · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
        have hc := odd_compl_of_even heven' hS
        have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          omega
        have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          have hle := Finset.card_le_univ S
          omega
        have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
        have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
        have hx1 := ih _ hlt1 (G.onSide S) rfl hv1 (G.restriction_mem_constraints hxQ S hS ht)
        have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
        have hx2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 (G.restriction_mem_constraints hxQ Sᶜ hc htc)
        obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hx1
        obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hx2
        exact (G.mem_polytope_iff x).mpr (G.couple_laws S x hp hq (congrFun hpx) (congrFun hqx))
      · obtain ⟨M,rfl⟩ := G.extreme_no_tight_integral heven' hx hcut
        exact subset_convexHull ℝ _ (Set.mem_range_self M)
    rw [← closure_convexHull_extremePoints G.isCompact_constraintPolytope G.convex_constraintPolytope]
    exact closure_minimal (convexHull_min hex (convex_convexHull ℝ _)) G.compact_polytope.isClosed

/-- Edmonds' perfect matching polytope equality, with parallel edges retained. -/
theorem polytope_eq_constraints (G : LooplessGraph V E) (heven : Even (Fintype.card V)) :
    G.polytope = G.constraintPolytope := by
  exact Set.Subset.antisymm G.polytope_subset_constraintPolytope
    (constraint_subset_polytope_aux (Fintype.card V) G rfl heven)

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Entropy
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite Shannon entropy and attainment of its supremum over feasible matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph


omit [Fintype E] [DecidableEq E] in
/-- Counting the two distinct endpoints; parallel identities are never collapsed. -/
theorem incident_vertex_sum (G : LooplessGraph V E) (e : E) :
    (∑ v, if G.Incident v e then (1 : ℕ) else 0) = 2 := by
  classical
  have he (v : V) : (if G.Incident v e then (1 : ℕ) else 0) =
      (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) := by
    by_cases hl : G.left e = v <;> by_cases hr : G.right e = v
    · exact False.elim (G.loopless e (hl.trans hr.symm))
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
  simp_rw [he, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incident_sum (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    (∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0) = 1 := by
  classical
  obtain ⟨e, ⟨he, hv⟩, hu⟩ := M.property v
  rw [Finset.sum_eq_single e]
  · simp [hv]
  · intro e' he' hne
    have hn : ¬ G.Incident v e' := fun hv' ↦ hne (hu e' ⟨he', hv'⟩)
    simp [hn]
  · simp [he]

omit [Fintype E] [DecidableEq E] in
theorem matching_card_twice (G : LooplessGraph V E) (M : G.Matching) :
    2 * M.val.card = Fintype.card V := by
  classical
  calc
    2 * M.val.card = ∑ e ∈ M.val, ∑ v, if G.Incident v e then (1 : ℕ) else 0 := by
      simp_rw [G.incident_vertex_sum]
      simp [Nat.mul_comm]
    _ = ∑ v, ∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by
      simp_rw [G.matching_incident_sum]
      simp

omit [Fintype E] [DecidableEq E] in
theorem matching_card (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) : M.val.card = m := by
  have h := G.matching_card_twice M
  omega

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_DyadicEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma log_two_pos : 0<Real.log 2 := Real.log_pos (by norm_num)

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_CompletePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching
noncomputable section
open Finset
variable {n : ℕ}

lemma sum_pairs (f : Fin n → Fin n → ℝ) :
    (∑ e : Pair n, f e.val.1 e.val.2)=∑ i,∑ j,if i < j then f i j else 0 := by
  let s : Finset (Fin n × Fin n) := univ.filter (fun ij => ij.1 < ij.2)
  have hs : ∀ ij : Fin n × Fin n,ij∈s ↔ ij.1 < ij.2 := by simp [s]
  rw [←sum_subtype s hs (fun ij => f ij.1 ij.2)]
  rw [show s=univ.filter (fun ij => ij.1 < ij.2) from rfl,sum_filter,Fintype.sum_prod_type]

lemma sum_skip (g : Fin n → ℝ) (v : Fin n) :
    (∑ j,if j=v then 0 else g j)=(∑ j,g j)-g v := by
  have hh : (∑ j,g j)=(∑ j,if j=v then 0 else g j)+g v := by
    calc
      _ = ∑ j, ((if j=v then 0 else g j)+(if j=v then g j else 0)) := by
        apply sum_congr rfl; intro j _; split_ifs <;> simp
      _ = _ := by rw [sum_add_distrib]; simp
  linarith

lemma degree_from_symm (f : Fin n → Fin n → ℝ) (hf : ∀ i j,f i j=f j i) (v : Fin n) :
    (completeGraph n).degree (fun e => f e.val.1 e.val.2) v =
      ∑ j,if j=v then 0 else f v j := by
  change (∑ e : Pair n,if e.val.1=v ∨ e.val.2=v then f e.val.1 e.val.2 else 0)=_
  rw [sum_pairs (fun i j => if i=v ∨ j=v then f i j else 0)]
  have he (i j : Fin n) :
      (if i < j then (if i=v ∨ j=v then f i j else 0) else 0) =
      (if i=v then (if i < j then f i j else 0) else 0)+
      (if j=v then (if i < j then f i j else 0) else 0) := by
    by_cases hiv : i=v <;> by_cases hjv : j=v <;> by_cases hij : i < j <;> simp_all
  simp_rw [he,sum_add_distrib]
  have hleft : (∑ i,∑ j,if i=v then (if i < j then f i j else 0) else 0)=
      ∑ j,if v < j then f v j else 0 := by
    simp [Finset.sum_ite_irrel]
  have hright : (∑ i,∑ j,if j=v then (if i < j then f i j else 0) else 0)=
      ∑ j,if j < v then f v j else 0 := by
    simp only [sum_ite_eq',mem_univ,ite_true]
    apply sum_congr rfl; intro j _; rw [hf j v]
  rw [hleft,hright,←sum_add_distrib]
  apply sum_congr rfl; intro j _
  rcases lt_trichotomy j v with h|h|h
  · simp [h, ne_of_lt h, not_lt_of_ge h.le]
  · subst j; simp
  · simp [h, ne_of_gt h, not_lt_of_ge h.le]

lemma degree_constant (b : ℝ) (v : Fin n) :
    (completeGraph n).degree (fun _ => b) v=((n:ℝ)-1)*b := by
  rw [degree_from_symm (fun _ _ => b) (fun _ _ => rfl),sum_skip]
  simp; ring

lemma cut_from_symm (f : Fin n → Fin n → ℝ) (hf : ∀ i j,f i j=f j i)
    (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => f e.val.1 e.val.2) S =
      ∑ i∈S,∑ j∈Sᶜ,f i j := by
  unfold MatchingEntropy.LooplessGraph.cutMass MatchingEntropy.LooplessGraph.cut
  rw [sum_filter]
  change (∑ e : Pair n,if (e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.1∉S ∧ e.val.2∈S)
    then f e.val.1 e.val.2 else 0)=_
  rw [sum_pairs (fun i j => if (i∈S ∧ j∉S) ∨ (i∉S ∧ j∈S) then f i j else 0)]
  have he (i j : Fin n) :
      (if i < j then (if (i∈S ∧ j∉S) ∨ (i∉S ∧ j∈S) then f i j else 0) else 0) =
        (if i < j ∧ i∈S ∧ j∉S then f i j else 0)+
        (if i < j ∧ i∉S ∧ j∈S then f i j else 0) := by
    by_cases hij : i < j <;> by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [hij,hi,hj]
  simp_rw [he,sum_add_distrib]
  have hswap : (∑ i,∑ j,if i < j ∧ i∉S ∧ j∈S then f i j else 0)=
      ∑ i,∑ j,if j < i ∧ i∈S ∧ j∉S then f i j else 0 := by
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    rw [hf j i]
    by_cases hij : j < i <;> by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [hij,hi,hj]
  rw [hswap,←sum_add_distrib]
  simp_rw [←sum_add_distrib]
  have hterm (i j : Fin n) :
      (if i < j ∧ i∈S ∧ j∉S then f i j else 0)+
        (if j < i ∧ i∈S ∧ j∉S then f i j else 0)=
        if i∈S ∧ j∉S then f i j else 0 := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_ge h.le]
    · subst j; simp
    · simp [h,not_lt_of_ge h.le]
  simp_rw [hterm]
  have hS : S=univ.filter (fun i => i∈S) := by ext i; simp
  have hSc : Sᶜ=univ.filter (fun j => j∉S) := by ext j; simp
  conv_rhs => rw [hS]; rw [sum_filter]
  simp only [ite_and]
  apply sum_congr rfl; intro i _
  by_cases hi : i∈S
  · simp only [hi,ite_true]
    rw [←hS,hSc,sum_filter]
  · simp only [hi,ite_false,sum_const_zero]

lemma cut_constant (b : ℝ) (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun _ => b) S=(S.card:ℝ)*(Sᶜ.card:ℝ)*b := by
  rw [cut_from_symm (fun _ _ => b) (fun _ _ => rfl)]
  simp [mul_assoc]

lemma q_le_square : Fintype.card (Pair n) ≤ n^2 := by
  calc
    _ ≤ Fintype.card (Fin n × Fin n) := Fintype.card_subtype_le _
    _ = n^2 := by simp [pow_two]

end
end BinaryMatching
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_FeasibilityRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

lemma uniform_box (hn : 4≤n) (e : Pair n) : uniform n e∈Set.Icc (0:ℝ) 1 := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (by norm_num) (by linarith)
  · exact (div_le_one (by linarith)).2 (by linarith)

lemma uniform_degree (hn : 4≤n) (v : Fin n) :
    (completeGraph n).degree (uniform n) v=1 := by
  unfold uniform
  rw [degree_constant]
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  field_simp [show (n:ℝ)-1≠0 by linarith]

lemma trivial_cut_degree {x : Pair n → ℝ} (hx : ∀ v,(completeGraph n).degree x v=1)
    {S : Finset (Fin n)} (hS : TrivialCut S) : (completeGraph n).cutMass x S=1 := by
  rcases hS with h|h
  · obtain ⟨v,rfl⟩ := card_eq_one.mp h
    simpa using hx v
  · obtain ⟨v,hv⟩ := card_eq_one.mp h
    have he : (completeGraph n).cutMass x S=(completeGraph n).cutMass x Sᶜ := by
      simp only [LooplessGraph.cutMass,LooplessGraph.cut_compl]
    rw [he,hv,LooplessGraph.cutMass_singleton,hx]

lemma uniform_nontrivial_cut (heven : Even n) {S : Finset (Fin n)} (hodd : Odd S.card)
    (hS : ¬TrivialCut S) : (3/2:ℝ)≤(completeGraph n).cutMass (uniform n) S := by
  have hcards : S.card+Sᶜ.card=n := by simp
  have ha : 3≤S.card := by
    have ho := Nat.odd_iff.mp hodd
    have hh : S.card≠1 := fun h => hS (Or.inl h)
    omega
  have hb : 3≤Sᶜ.card := by
    have ho := Nat.odd_iff.mp hodd
    have he := Nat.even_iff.mp heven
    have hh : Sᶜ.card≠1 := fun h => hS (Or.inr h)
    omega
  have ha' : (3:ℝ)≤S.card := by exact_mod_cast ha
  have hb' : (3:ℝ)≤Sᶜ.card := by exact_mod_cast hb
  have hc' : (S.card:ℝ)+Sᶜ.card=n := by exact_mod_cast hcards
  have hn : (6:ℝ)≤n := by linarith
  unfold uniform
  rw [cut_constant]
  rw [mul_one_div,le_div_iff₀ (by linarith : 0<(n:ℝ)-1)]
  have hp := mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')
  nlinarith

lemma uniform_feasible (hn : 4≤n) (heven : Even n) :
    uniform n∈(completeGraph n).polytope := by
  rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)]
  refine ⟨fun e => (uniform_box hn e).1,uniform_degree hn,?_⟩
  intro S hS
  by_cases ht : TrivialCut S
  · rw [trivial_cut_degree (uniform_degree hn) ht]
  · linarith [uniform_nontrivial_cut heven hS ht]

end
end BinaryMatching
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Partition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open Finset
namespace MatchingEntropy

variable {I : Type*} [Fintype I]

lemma expSum_pos [Nonempty I] (a : I → ℝ) : 0<expSum a :=
  sum_pos (fun i _ => Real.exp_pos (a i)) univ_nonempty

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_AlgorithmPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma complete_matching_nonempty {n : ℕ} (hn : 4≤ n) (heven : Even n) :
    Nonempty (completeGraph n).Matching := by
  obtain ⟨p,hp⟩ := ((completeGraph n).mem_polytope_iff _).mp (uniform_feasible hn heven)
  by_contra h
  have : IsEmpty (completeGraph n).Matching := not_nonempty_iff.mp h
  simpa using hp.1.2

lemma Z_pos (G : Input) (hn : 4≤ G.n) (heven : Even G.n) : 0< Z G := by
  have := complete_matching_nonempty hn heven
  exact expSum_pos _

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma matchingWeight_exp (G : Input) (M : (completeGraph G.n).Matching) :
    matchingWeight G M=Real.exp (Real.log 2*((completeGraph G.n).score (fun e => (beta G e:ℝ)) M)) := by
  rw [LooplessGraph.score,mul_sum,Real.exp_sum]
  rfl

lemma matchingWeight_pos (G : Input) (M : (completeGraph G.n).Matching) : 0< matchingWeight G M := by
  rw [matchingWeight_exp]; exact Real.exp_pos _

lemma Z_decompose (G : Input) : Z G=Zgood G+Zbad G := by
  unfold Z LooplessGraph.weightedZ expSum Zgood Zbad
  rw [←sum_add_distrib]
  apply sum_congr rfl; intro M _
  rw [←matchingWeight_exp]
  unfold goodWeight badWeight
  split_ifs <;> simp

lemma goodWeight_nonneg (G : Input) (M : (completeGraph G.n).Matching) : 0≤ goodWeight G M := by
  unfold goodWeight; split_ifs
  · exact (matchingWeight_pos G M).le
  · rfl

lemma badWeight_nonneg (G : Input) (M : (completeGraph G.n).Matching) : 0≤ badWeight G M := by
  unfold badWeight; split_ifs
  · rfl
  · exact (matchingWeight_pos G M).le

lemma Zgood_nonneg (G : Input) : 0≤ Zgood G := sum_nonneg fun M _ => goodWeight_nonneg G M
lemma Zbad_nonneg (G : Input) : 0≤ Zbad G := sum_nonneg fun M _ => badWeight_nonneg G M

lemma edgeWeight_present (G : Input) (e : Pair G.n) (he : 0< multiplicity G e) :
    edgeWeight G e=(2:ℝ)^Nat.log2 (multiplicity G e) := by
  rw [edgeWeight,beta,ite_eq_right (by omega),Int.cast_natCast,mul_comm,Real.exp_nat_mul]
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)]

lemma edgeWeight_rounding (G : Input) (e : Pair G.n) (he : 0< multiplicity G e) :
    (multiplicity G e:ℝ)/2≤ edgeWeight G e ∧ edgeWeight G e≤(multiplicity G e:ℝ) := by
  rw [edgeWeight_present G e he]
  have hlo := Nat.log2_self_le (show multiplicity G e≠0 by omega)
  have hhi : multiplicity G e<2^(Nat.log2 (multiplicity G e)+1) := Nat.lt_log2_self
  have hlo' : (2:ℝ)^Nat.log2 (multiplicity G e)≤(multiplicity G e:ℝ) := by exact_mod_cast hlo
  have hhi' : (multiplicity G e:ℝ)<(2:ℝ)^(Nat.log2 (multiplicity G e)+1) := by exact_mod_cast hhi
  rw [pow_succ] at hhi'
  constructor <;> linarith

lemma invalid_product_zero (G : Input) (M : (completeGraph G.n).Matching)
    (hM : ¬validMatching G M) : multProduct G M=0 := by
  classical
  unfold validMatching at hM
  push Not at hM
  obtain ⟨e,he,hzero⟩ := hM
  unfold multProduct
  exact prod_eq_zero he (by omega)

lemma goodWeight_le_product (G : Input) (M : (completeGraph G.n).Matching) :
    goodWeight G M≤(multProduct G M:ℝ) := by
  unfold goodWeight
  split_ifs with hM
  · unfold matchingWeight multProduct
    push_cast
    exact prod_le_prod (fun e _ => (Real.exp_pos _).le)
      (fun e he => (edgeWeight_rounding G e (hM e he)).2)
  · positivity

lemma goodWeight_ge_product (G : Input) (M : (completeGraph G.n).Matching) :
    (2:ℝ)⁻¹^M.val.card*(multProduct G M:ℝ)≤ goodWeight G M := by
  unfold goodWeight
  split_ifs with hM
  · calc
      _ = ∏ e∈M.val,((multiplicity G e:ℝ)/2) := by
        simp only [div_eq_mul_inv,prod_mul_distrib,prod_const,multProduct,Nat.cast_prod]
        ring
      _ ≤ _ := prod_le_prod (fun e _ => by positivity)
        (fun e he => (edgeWeight_rounding G e (hM e he)).1)
  · rw [invalid_product_zero G M hM,Nat.cast_zero,mul_zero]

lemma Zgood_bracket (G : Input) {r : ℕ} (hn : G.n=2*r) :
    (2:ℝ)⁻¹^r*(count G:ℝ)≤ Zgood G ∧ Zgood G≤(count G:ℝ) := by
  have hc (M : (completeGraph G.n).Matching) : M.val.card=r :=
    (completeGraph G.n).matching_card (by simpa) M
  have hncast : (count G:ℝ)=∑ M,(multProduct G M:ℝ) := by simp [count,multProduct]
  rw [hncast]
  constructor
  · rw [mul_sum]
    exact sum_le_sum fun M _ => by simpa only [hc M] using goodWeight_ge_product G M
  · exact sum_le_sum fun M _ => goodWeight_le_product G M

lemma positive_count_valid (G : Input) (hN : 0< count G) :
    ∃ M : (completeGraph G.n).Matching, validMatching G M := by
  have hsum : 0<∑ M,multProduct G M := hN
  obtain ⟨M,_hM,hprod⟩ := (sum_pos_iff_of_nonneg (fun M _ => Nat.zero_le (multProduct G M))).mp hsum
  refine ⟨M,?_⟩
  by_contra h
  rw [invalid_product_zero G M h] at hprod
  omega

lemma validWeight_ge_one (G : Input) (M : (completeGraph G.n).Matching)
    (hM : validMatching G M) : 1≤ goodWeight G M := by
  rw [goodWeight,ite_eq_left hM]
  apply one_le_prod
  intro e he
  rw [edgeWeight_present G e (hM e he)]
  exact one_le_pow₀ (by norm_num)

lemma Zgood_ge_one (G : Input) (hN : 0< count G) : 1≤ Zgood G := by
  obtain ⟨M,hM⟩ := positive_count_valid G hN
  exact (validWeight_ge_one G M hM).trans
    (single_le_sum (fun N _ => goodWeight_nonneg G N) (mem_univ M))

lemma beta_le_B (G : Input) (e : Pair G.n) : (beta G e:ℝ)≤(B G:ℝ) := by
  unfold beta
  split_ifs
  · simp only [Int.cast_neg,Int.cast_natCast]
    have : (0:ℝ)≤ B G := by positivity
    have : (0:ℝ)≤ L G := by positivity
    linarith
  · exact_mod_cast multiplicity_log_le_B G e

lemma matching_card_bound (n : ℕ) : Fintype.card (completeGraph n).Matching≤2^(q n) := by
  calc
    _ ≤ Fintype.card (Finset (Pair n)) :=
      Fintype.card_le_of_injective (fun M => M.val) Subtype.val_injective
    _ = _ := by rw [Fintype.card_finset]; rfl

lemma badWeight_bound (G : Input) {r : ℕ} (hn : G.n=2*r)
    (M : (completeGraph G.n).Matching) :
    badWeight G M≤ Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by
  classical
  unfold badWeight
  split_ifs with hM
  · exact (Real.exp_pos _).le
  · have hbad := hM
    unfold validMatching at hbad
    push Not at hbad
    obtain ⟨e,he,hzero⟩ := hbad
    have hz : multiplicity G e=0 := by omega
    have hbe : (beta G e:ℝ)=-(L G:ℝ) := by simp [beta,hz]
    have hc : M.val.card=r := (completeGraph G.n).matching_card (by simpa) M
    have hsingle := single_le_sum (s := M.val) (f := fun e => (B G:ℝ)-(beta G e:ℝ))
      (fun e _ => sub_nonneg.mpr (beta_le_B G e)) he
    rw [hbe,sum_sub_distrib,sum_const,hc,nsmul_eq_mul] at hsingle
    have hB : (0:ℝ)≤ B G := by positivity
    have hsum : (∑ e∈M.val,(beta G e:ℝ))≤(B G:ℝ)*r-L G := by nlinarith
    rw [matchingWeight_exp]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsum log_two_pos.le

lemma Zbad_bound (G : Input) {r : ℕ} (hn : G.n=2*r) :
    Zbad G≤ Real.exp (Real.log 2*((q G.n:ℝ)+(B G:ℝ)*r-L G)) := by
  calc
    _ ≤ ∑ _M : (completeGraph G.n).Matching, Real.exp (Real.log 2*((B G:ℝ)*r-L G)) :=
      sum_le_sum fun M _ => badWeight_bound G hn M
    _ = (Fintype.card (completeGraph G.n).Matching:ℝ)*Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by simp
    _ ≤ (2:ℝ)^(q G.n)*Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast matching_card_bound G.n
    _ = _ := by
      have he : (2:ℝ)^(q G.n)=Real.exp ((q G.n:ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      rw [he,←Real.exp_add]
      congr 1
      ring

lemma completion_parameter_bound (G : Input) {r : ℕ} (hn : G.n=2*r) :
    q G.n+B G*r+20*G.n≤ L G := by
  let t := G.n+B G+1
  have ht1 : 1≤ t := by dsimp [t]; omega
  have hnt : G.n≤ t := by dsimp [t]; omega
  have hBt : B G≤ t := by dsimp [t]; omega
  have hrt : r≤ t := by omega
  have hq : q G.n≤ t^2 := (q_le_square (n := G.n)).trans (Nat.pow_le_pow_left hnt 2)
  have hBr : B G*r≤ t^2 := by simpa only [pow_two] using Nat.mul_le_mul hBt hrt
  have ht13 : t≤ t^3 := Nat.le_self_pow (by omega) t
  have ht23 : t^2≤ t^3 := by
    calc
      t^2=t^2*1 := by ring
      _ ≤ t^2*t := Nat.mul_le_mul_left _ ht1
      _ = _ := by ring
  change _≤100*t^3
  omega

lemma Zbad_small (G : Input) (heven : Even G.n) :
    Zbad G≤ Real.exp (Real.log 2*(-20*(G.n:ℝ))) := by
  obtain ⟨r,hr⟩ := heven
  have hn : G.n=2*r := by omega
  have hh := Zbad_bound G hn
  have hdom : (q G.n:ℝ)+(B G:ℝ)*r+20*(G.n:ℝ)≤ L G := by
    exact_mod_cast completion_parameter_bound G hn
  apply hh.trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ log_two_pos.le
  linarith

theorem completion_bracket (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    (count G=0 → logZ G≤-20*(G.n:ℝ)) ∧
    (0< count G → 1≤ Z G ∧ (2:ℝ)⁻¹^(G.n/2)*(count G:ℝ)≤ Z G ∧ Z G≤2*(count G:ℝ)) := by
  have hbad := Zbad_small G heven
  have hNsplit := Z_decompose G
  have hsmall : Zbad G≤1 := by
    apply hbad.trans (Real.exp_le_one_iff.mpr _)
    exact mul_nonpos_of_nonneg_of_nonpos log_two_pos.le (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hn2 : G.n=2*(G.n/2) := by
    obtain ⟨r,hr⟩ := heven
    omega
  have hgood := Zgood_bracket G hn2
  constructor
  · intro hN
    have hg : Zgood G=0 := le_antisymm (by simpa only [hN,Nat.cast_zero] using hgood.2) (Zgood_nonneg G)
    have hz : Z G≤ Real.exp (Real.log 2*(-20*(G.n:ℝ))) := by linarith
    have hl := Real.log_le_log (Z_pos G hn heven) hz
    rw [Real.log_exp] at hl
    unfold logZ
    apply (div_le_iff₀ log_two_pos).2
    nlinarith
  · intro hN
    have hng : 1≤ Zgood G := Zgood_ge_one G hN
    have hN' : (1:ℝ)≤ count G := by exact_mod_cast hN
    have hbn := Zbad_nonneg G
    constructor
    · linarith
    constructor
    · linarith [hgood.1]
    · linarith [hgood.2]

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_CountCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma zero_test (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    R G < -10*(G.n:ℤ) ↔ count G = 0 := by
  have hp := R_partition_bracket G hn heven
  have hc := completion_bracket G hn heven
  have hn' : (4:ℝ) ≤ G.n := by exact_mod_cast hn
  constructor
  · intro hr
    by_contra hN
    have hNpos : 0 < count G := Nat.pos_of_ne_zero hN
    have hz : 0 ≤ logZ G := by
      unfold logZ
      exact div_nonneg (Real.log_nonneg (hc.2 hNpos).1) log_two_pos.le
    have hr' : (R G:ℝ) < -10*(G.n:ℝ) := by exact_mod_cast hr
    linarith [hp.2]
  · intro hN
    have hz := hc.1 hN
    have hr' : (R G:ℝ) < -10*(G.n:ℝ) := by linarith [hp.1]
    exact_mod_cast hr'

lemma log_count_bracket (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n)
    (hN : 0 < count G) :
    (R G:ℝ)-5*(G.n:ℝ) ≤ Real.log (count G)/Real.log 2 ∧
      Real.log (count G)/Real.log 2 ≤ (R G:ℝ)+4*(G.n:ℝ) := by
  have hp := R_partition_bracket G hn heven
  obtain ⟨_hone,hlo,hhi⟩ := (completion_bracket G hn heven).2 hN
  have hN' : (0:ℝ) < count G := by exact_mod_cast hN
  have hn' : (4:ℝ) ≤ G.n := by exact_mod_cast hn
  have hlo' := Real.log_le_log (show (0:ℝ) < 2⁻¹^(G.n/2)*(count G:ℝ) by positivity) hlo
  have hhi' := Real.log_le_log (Z_pos G hn heven) hhi
  rw [Real.log_mul (by positivity) hN'.ne',Real.log_pow,Real.log_inv] at hlo'
  rw [Real.log_mul (by norm_num) hN'.ne'] at hhi'
  have hdiv : ((G.n/2:ℕ):ℝ) ≤ (G.n:ℝ) := by exact_mod_cast Nat.div_le_self G.n 2
  dsimp only [logZ] at hp
  constructor
  · apply (le_div_iff₀ log_two_pos).2
    have hpart := (le_div_iff₀ log_two_pos).1 hp.1
    nlinarith [log_two_pos]
  · apply (div_le_iff₀ log_two_pos).2
    have hpart := (div_le_iff₀ log_two_pos).1 hp.2
    nlinarith [mul_le_mul_of_nonneg_right hdiv log_two_pos.le]

theorem estimate_correct (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    estimate G ≤ count G ∧ count G ≤ 2^(9*G.n)*estimate G ∧
      (estimate G=0 ↔ count G=0) := by
  by_cases hN : count G=0
  · have hr : R G < -(10*(G.n:ℤ)) := by simpa only [neg_mul] using (zero_test G hn heven).2 hN
    simp [estimate,hr,hN]
  · have hNpos : 0 < count G := Nat.pos_of_ne_zero hN
    have hr : ¬R G < -(10*(G.n:ℤ)) := by simpa only [←neg_mul,zero_test G hn heven] using hN
    have he : estimate G=2^(R G-5*(G.n:ℤ)).toNat := by simp [estimate,hr]
    let rho := (R G-5*(G.n:ℤ)).toNat
    have he' : estimate G=2^rho := he
    have hrhol : (R G:ℝ)-5*(G.n:ℝ) ≤ (rho:ℝ) := by
      have hi : R G-5*(G.n:ℤ) ≤ (rho:ℤ) := Int.self_le_toNat _
      exact_mod_cast hi
    have hNc : (0:ℝ) < count G := by exact_mod_cast hNpos
    have hN1 : (1:ℝ) ≤ count G := by exact_mod_cast hNpos
    have hlog0 : 0 ≤ Real.log (count G)/Real.log 2 :=
      div_nonneg (Real.log_nonneg hN1) log_two_pos.le
    have hbracket := log_count_bracket G hn heven hNpos
    have hrhou : (rho:ℝ) ≤ Real.log (count G)/Real.log 2 := by
      by_cases hnon : 0 ≤ R G-5*(G.n:ℤ)
      · have hh : (rho:ℤ)=R G-5*(G.n:ℤ) := Int.toNat_of_nonneg hnon
        have hh' : (rho:ℝ)=(R G:ℝ)-5*(G.n:ℝ) := by exact_mod_cast hh
        rw [hh']; exact hbracket.1
      · have hz : rho=0 := Int.toNat_of_nonpos (by omega)
        simpa only [hz,Nat.cast_zero] using hlog0
    have hlow : (2:ℝ)^rho ≤ (count G:ℝ) := by
      apply (Real.log_le_log_iff (by positivity) hNc).1
      rw [Real.log_pow]
      exact (le_div_iff₀ log_two_pos).1 hrhou
    have hupp : (count G:ℝ) ≤ (2:ℝ)^(9*G.n)*(2:ℝ)^rho := by
      apply (Real.log_le_log_iff hNc (by positivity)).1
      rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
      have hh : Real.log (count G)/Real.log 2 ≤ (9*G.n:ℕ)+(rho:ℝ) := by
        push_cast; linarith [hbracket.2]
      have hh' := (div_le_iff₀ log_two_pos).1 hh
      push_cast at hh' ⊢
      nlinarith
    have hlow' : 2^rho ≤ count G := by exact_mod_cast hlow
    have hupp' : count G ≤ 2^(9*G.n)*2^rho := by exact_mod_cast hupp
    rw [he']
    refine ⟨hlow',hupp',?_⟩
    simp [hN]

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_ElementaryCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma count_zero_vertices (G : Input) (hn : G.n=0) : count G=1 := by
  classical
  let M : (completeGraph G.n).Matching := ⟨∅,fun v => by have := v.isLt; omega⟩
  have hM (N : (completeGraph G.n).Matching) : N=M := by
    apply Subtype.ext
    apply Finset.eq_empty_of_forall_notMem
    intro e _
    have := e.val.1.isLt
    omega
  unfold count
  rw [sum_eq_single M]
  · simp [M]
  · intro N _ hne
    exact (hne (hM N)).elim
  · simp

lemma count_odd_vertices (G : Input) (hn : Odd G.n) : count G=0 := by
  classical
  have hempty : IsEmpty (completeGraph G.n).Matching := ⟨fun M => by
    have hh := (completeGraph G.n).matching_card_twice M
    simp only [Fintype.card_fin] at hh
    obtain ⟨r,hr⟩ := hn
    omega⟩
  simp [count]

lemma count_two_vertices (G : Input) (hn : G.n=2) : count G=rawMultiplicity G 0 1 := by
  classical
  let e : Pair G.n := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp⟩
  have heq (f : Pair G.n) : f=e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · have hh := f.property; have h1 := f.val.1.isLt; have h2 := f.val.2.isLt
      dsimp [e] at hh ⊢; omega
    · have hh := f.property; have h1 := f.val.1.isLt; have h2 := f.val.2.isLt
      dsimp [e] at hh ⊢; omega
  have heinc (v : Fin G.n) : (completeGraph G.n).Incident v e := by
    have hv := v.isLt
    change e.val.1=v ∨ e.val.2=v
    by_cases hz : v.val=0
    · left; apply Fin.ext; exact hz.symm
    · right; apply Fin.ext; dsimp [e]; omega
  let M : (completeGraph G.n).Matching := ⟨{e},fun v => ⟨e,⟨by simp,heinc v⟩,
    fun _ h => by simpa only [mem_singleton] using h.1⟩⟩
  have hM (N : (completeGraph G.n).Matching) : N=M := by
    apply Subtype.ext
    apply Finset.ext
    intro f
    have hfn := heq f
    obtain ⟨g,hg,_⟩ := N.property e.val.1
    have hgn := heq g
    have hmem : e∈N.val := hgn ▸ hg.1
    simp only [M,mem_singleton,hfn]
    exact iff_true_intro hmem
  unfold count
  rw [sum_eq_single M]
  · simp only [M,prod_singleton]
    unfold multiplicity rawMultiplicity
    dsimp [e]
    cases G.records.find? (fun r => r.left=0 && r.right=1) <;> rfl
  · intro N _ hne
    exact (hne (hM N)).elim
  · simp

lemma present_endpoints_covered (G : Input) (e : Pair G.n) (he : 0 < multiplicity G e) :
    e.val.1.val∈covered G ∧ e.val.2.val∈covered G := by
  unfold multiplicity at he
  cases hf : G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => simp only [hf] at he; omega
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hp
    simp only [hf] at he
    have hr' : r∈G.records.filter (fun r => 0 < r.multiplicity) := by simp [hr,he]
    constructor
    · simp only [covered,List.mem_toFinset,List.mem_flatMap]
      refine ⟨r,hr',?_⟩
      simp [hp.1]
    · simp only [covered,List.mem_toFinset,List.mem_flatMap]
      refine ⟨r,hr',?_⟩
      simp [hp.2]

lemma positive_count_covered (G : Input) (hN : 0 < count G) : G.n ≤ (covered G).card := by
  obtain ⟨M,hM⟩ := positive_count_valid G hN
  have hsub : range G.n ⊆ covered G := by
    intro v hv
    let w : Fin G.n := ⟨v,mem_range.mp hv⟩
    obtain ⟨e,⟨he,hinc⟩,_⟩ := M.property w
    have hep := present_endpoints_covered G e (hM e he)
    rcases hinc with h|h
    · have hh : e.val.1.val=v := congrArg Fin.val h
      simpa only [hh] using hep.1
    · have hh : e.val.2.val=v := congrArg Fin.val h
      simpa only [hh] using hep.2
  simpa only [card_range] using card_le_card hsub

lemma count_zero_of_uncovered (G : Input) (hu : (covered G).card < G.n) : count G=0 := by
  by_contra hN
  have := positive_count_covered G (Nat.pos_of_ne_zero hN)
  omega

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_SizeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma covered_card_le_records (G : Input) : (covered G).card≤2*G.records.length := by
  have hh := List.toFinset_card_le
    ((G.records.filter (fun e => 0< e.multiplicity)).flatMap (fun e => [e.left,e.right]))
  have hlen : ((G.records.filter (fun e => 0< e.multiplicity)).flatMap (fun e => [e.left,e.right])).length=
      2*(G.records.filter (fun e => 0< e.multiplicity)).length := by
    rw [List.length_flatMap]
    simp
    omega
  rw [hlen] at hh
  exact hh.trans (Nat.mul_le_mul_left 2 (List.length_filter_le _ _))

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ScaledState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm

lemma integralIterate_best (G : Input) (hn : 2≤G.n) (j : ℕ) :
    ((integralIterate G j).best.map (fun v : ℤ => (v:ℚ)/(Q G:ℚ)))=(iterate G j).best :=
  congrArg State.best (decodeIntegral_iterate G hn j)

lemma integralR_eq (G : Input) (hn : 2≤G.n) : integralR G=R G := by
  unfold integralR R
  rw [←integralIterate_best G hn]
  cases h : (integralIterate G (q G.n*D₀ G)).best with
  | none => simp
  | some v => simp only [Option.getD_some,Option.map_some,Int.floor_div_natCast,Int.floor_intCast]

lemma integralEstimate_eq (G : Input) (hn : 2≤G.n) : integralEstimate G=estimate G := by
  simp only [integralEstimate,estimate,integralR_eq G hn]

end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_BinarySolve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.InputData
open StackCode Algorithm Optimize

lemma sparseEstimate_correct (G : Input) :
    sparseEstimate G≤count G ∧ count G≤2^(9*G.n)*sparseEstimate G ∧ (sparseEstimate G=0 ↔ count G=0) := by
  unfold sparseEstimate
  split_ifs with hguard
  · have hz := count_zero_of_uncovered G (lt_of_le_of_lt (covered_card_le_records G) hguard)
    simp [hz]
  · unfold smallEstimate
    split_ifs with hn0 hodd hn2
    · rw [count_zero_vertices G hn0,hn0]
      norm_num
    · rw [count_odd_vertices G (Nat.odd_iff.mpr hodd)]
      simp
    · rw [count_two_vertices G hn2]
      refine ⟨le_rfl,?_,Iff.rfl⟩
      exact Nat.le_mul_of_pos_left _ (by positivity)
    · have hn : 4≤G.n := by omega
      have he : Even G.n := Nat.even_iff.mpr (by omega)
      rw [integralEstimate_eq G (by omega)]
      exact estimate_correct G hn he

end BinaryMatching.Raw.InputData

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_Approximation
attribute [-instance] _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching
open scoped BigOperators

namespace Approximation

theorem term_bounds (G : Input) (j : ℕ) :
    term G j ≤ BinaryMatching.count (expand G j) ∧
    BinaryMatching.count (expand G j) ≤ 2 ^ (9 * (G.n + j)) * term G j ∧
    (term G j = 0 ↔ BinaryMatching.count (expand G j) = 0) := by
  simpa only [term, expand_n] using
    BinaryMatching.Raw.InputData.sparseEstimate_correct (expand G j)

theorem output_den_pos (G : Input) : 0 < (output G).2 := Nat.factorial_pos _

theorem factorial_profile_bounds (a b : ℕ → ℕ) (C n : ℕ)
    (hlo : ∀ j ≤ n, a j ≤ j.factorial * b j)
    (hhi : ∀ j ≤ n, j.factorial * b j ≤ C * a j) :
    Accumulator.Q a n ≤ n.factorial * (∑ j ∈ Finset.range (n + 1), b j) ∧
    n.factorial * (∑ j ∈ Finset.range (n + 1), b j) ≤ C * Accumulator.Q a n := by
  revert hlo hhi
  induction n with
  | zero =>
      intro hlo hhi
      simpa using And.intro (hlo 0 (by omega)) (hhi 0 (by omega))
  | succ n ih =>
      intro hlo hhi
      obtain ⟨hl, hu⟩ := ih (fun j hj => hlo j (by omega))
        (fun j hj => hhi j (by omega))
      have hlastlo := hlo (n + 1) (by omega)
      have hlasthi := hhi (n + 1) (by omega)
      rw [Accumulator.Q_succ, Finset.sum_range_succ]
      constructor
      · calc
          (n + 1) * Accumulator.Q a n + a (n + 1) ≤
              (n + 1) * (n.factorial * (∑ j ∈ Finset.range (n + 1), b j)) +
                (n + 1).factorial * b (n + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hl) hlastlo
          _ = (n + 1).factorial *
              ((∑ j ∈ Finset.range (n + 1), b j) + b (n + 1)) := by
            rw [Nat.factorial_succ]; ring
      · calc
          (n + 1).factorial *
              ((∑ j ∈ Finset.range (n + 1), b j) + b (n + 1)) =
              (n + 1) * (n.factorial * (∑ j ∈ Finset.range (n + 1), b j)) +
                (n + 1).factorial * b (n + 1) := by
            rw [Nat.factorial_succ]; ring
          _ ≤ (n + 1) * (C * Accumulator.Q a n) + C * a (n + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hu) hlasthi
          _ = C * ((n + 1) * Accumulator.Q a n + a (n + 1)) := by ring

theorem output_bounds_of_expanded_count (G : Input)
    (expanded_count : ∀ j ≤ G.n,
      BinaryMatching.count (expand G j) = j.factorial * countWithLoops G j) :
    (output G).1 ≤ (output G).2 * count G ∧
    (output G).2 * count G ≤ 2 ^ (18 * G.n) * (output G).1 ∧
    ((output G).1 = 0 ↔ count G = 0) := by
  have hlo : ∀ j ≤ G.n, term G j ≤ j.factorial * countWithLoops G j := by
    intro j hj
    rw [← expanded_count j hj]
    exact (term_bounds G j).1
  have hhi : ∀ j ≤ G.n,
      j.factorial * countWithLoops G j ≤ 2 ^ (18 * G.n) * term G j := by
    intro j hj
    rw [← expanded_count j hj]
    apply (term_bounds G j).2.1.trans
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ))
    omega
  obtain ⟨hl, hu⟩ := factorial_profile_bounds (term G) (countWithLoops G)
    (2 ^ (18 * G.n)) G.n hlo hhi
  rw [← count_eq_sum_countWithLoops G] at hl hu
  change (output G).1 ≤ (output G).2 * count G at hl
  change (output G).2 * count G ≤ 2 ^ (18 * G.n) * (output G).1 at hu
  refine ⟨hl, hu, ?_⟩
  constructor
  · intro hz
    rw [hz, mul_zero] at hu
    have hprod : (output G).2 * count G = 0 := Nat.eq_zero_of_le_zero hu
    exact (Nat.mul_eq_zero.mp hprod).resolve_left (Nat.ne_of_gt (output_den_pos G))
  · intro hz
    rw [hz, mul_zero] at hl
    exact Nat.eq_zero_of_le_zero hl

end Approximation
end LoopMatching

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_ChoiceCounts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

theorem card_dummyAssignments {n : ℕ} (M : PartialMatching n) (j : ℕ) :
    Fintype.card (Fin j ≃ ↥(loopVertices M)) =
      if (loopVertices M).card = j then j.factorial else 0 := by
  classical
  by_cases h : (loopVertices M).card = j
  · rw [ite_eq_left h]
    let e : Fin j ≃ ↥(loopVertices M) := Fintype.equivOfCardEq (by
      simpa only [Fintype.card_fin, Fintype.card_coe] using h.symm)
    simpa only [Fintype.card_fin] using Fintype.card_equiv e
  · rw [ite_eq_right h]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun e => h (by
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        (Fintype.card_congr e).symm)⟩

end LoopMatching

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_ExpandBijection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

lemma supportedMatchingEquiv_fst (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    (supportedMatchingEquiv G j N).1 = restrictMatching G j N := by
  have hh := congrArg (restrictMatching G j) ((assembleMatchingEquiv G j).apply_symm_apply N)
  change restrictMatching G j (assembleMatching G j
    (supportedMatchingEquiv G j N).1 (supportedMatchingEquiv G j N).2) = _ at hh
  simpa only [restrict_assemble] using hh

lemma supported_matching_weight (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    (∏ e ∈ N.val.val, BinaryMatching.multiplicity (expand G j) e) =
      weight G (restrictMatching G j N) := by
  classical
  rw [← Finset.prod_coe_sort]
  have hprod := Fintype.prod_equiv (supportedEdgeEquiv G j N)
    (fun x => match x with
      | Sum.inl e => BinaryMatching.multiplicity G.ordinary e.val
      | Sum.inr d => loopMultiplicity G (crossPartner G j N d))
    (fun e : N.val.val => BinaryMatching.multiplicity (expand G j) e.val)
    (by
      intro x
      cases x with
      | inl e =>
        change BinaryMatching.multiplicity G.ordinary e.val =
          BinaryMatching.multiplicity (expand G j) (oldPair G j e.val)
        exact (multiplicity_expand_old G j e.val).symm
      | inr d =>
        change loopMultiplicity G (crossPartner G j N d) =
          BinaryMatching.multiplicity (expand G j) (crossPair G j (crossPartner G j N d) d)
        exact (multiplicity_expand_cross G j (crossPartner G j N d) d).symm)
  rw [← hprod,Fintype.prod_sum_type]
  have hloop := Fintype.prod_equiv (dummyEquiv G j N)
    (fun d => loopMultiplicity G (crossPartner G j N d))
    (fun v => loopMultiplicity G v.val) (fun _ => rfl)
  rw [hloop]
  simp only [Finset.prod_coe_sort,weight]

end LoopMatching

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_ExpandCount
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

lemma expanded_weight_zero_of_not_supported (G : Input) (j : ℕ)
    (N : (BinaryMatching.completeGraph (expand G j).n).Matching)
    (h : ¬ ∀ e ∈ N.val, e.val.1.val < G.n) :
    (∏ e ∈ N.val, BinaryMatching.multiplicity (expand G j) e) = 0 := by
  classical
  push Not at h
  obtain ⟨e, he, hl⟩ := h
  have heleft := e.val.1.isLt
  have heright := e.val.2.isLt
  have hord := e.property
  change e.val.1.val < e.val.2.val at hord
  simp only [expand_n] at heleft heright
  let f : BinaryMatching.Pair j :=
    ⟨(⟨e.val.1.val - G.n, by omega⟩,
      ⟨e.val.2.val - G.n, by omega⟩), by
        change e.val.1.val - G.n < e.val.2.val - G.n
        omega⟩
  have hf : dummyPair G j f = e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · dsimp [dummyPair, f]; omega
    · dsimp [dummyPair, f]; omega
  apply Finset.prod_eq_zero he
  rw [← hf]
  exact multiplicity_expand_dummy G j f

theorem expanded_count (G : Input) (j : ℕ) :
    BinaryMatching.count (expand G j) = j.factorial * countWithLoops G j := by
  classical
  let w : (BinaryMatching.completeGraph (expand G j).n).Matching → ℕ :=
    fun N => ∏ e ∈ N.val, BinaryMatching.multiplicity (expand G j) e
  have hzero :
      (∑ N : {N : (BinaryMatching.completeGraph (expand G j).n).Matching //
        ¬ ∀ e ∈ N.val, e.val.1.val < G.n}, w N.val) = 0 := by
    apply Finset.sum_eq_zero
    intro N _
    exact expanded_weight_zero_of_not_supported G j N.val N.property
  have hs : BinaryMatching.count (expand G j) =
      ∑ N : SupportedMatching G j, w N.val := by
    have ht := Fintype.sum_subtype_add_sum_subtype
      (fun N : (BinaryMatching.completeGraph (expand G j).n).Matching =>
        ∀ e ∈ N.val, e.val.1.val < G.n) w
    rw [hzero, Nat.add_zero] at ht
    have hi :
        (Subtype.fintype (fun N :
          (BinaryMatching.completeGraph (expand G j).n).Matching =>
            ∀ e ∈ N.val, e.val.1.val < G.n) : Fintype (SupportedMatching G j)) =
          supportedMatchingFintype G j := Subsingleton.elim _ _
    rw [hi] at ht
    exact ht.symm
  rw [hs]
  calc
    _ = ∑ q : (M : PartialMatching G.n) × (Fin j ≃ ↥(loopVertices M)),
        weight G q.1 := by
      apply Fintype.sum_equiv (supportedMatchingEquiv G j)
      intro N
      rw [supportedMatchingEquiv_fst]
      exact supported_matching_weight G j N
    _ = ∑ M : PartialMatching G.n,
        Fintype.card (Fin j ≃ ↥(loopVertices M)) * weight G M := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro M _
      simp
    _ = j.factorial * countWithLoops G j := by
      unfold countWithLoops
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      rw [card_dummyAssignments]
      by_cases h : (loopVertices M).card = j <;> simp [h]

end LoopMatching

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_MachineMain
attribute [-instance] _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.MachineMain
open BinaryMatching.StackCode

theorem computational_endpoint :
    ∃ machine : Turing.TM2ComputableInPolyTime encodeInput encodeOutput A,
      (∀ k, Finite (machine.tm.Γ k)) ∧
      (∃ P : Polynomial ℕ, ∀ G,
        (encodeOutput (A G)).length ≤ P.eval (encodeInput G).length) := by
  refine ⟨countingRoutine.machine,countingRoutine.machine_alphabets_finite,?_⟩
  refine ⟨Polynomial.X+countingRoutine.time,?_⟩
  intro G
  simpa only [Polynomial.eval_add,Polynomial.eval_X] using countingRoutine.length_bound G

end LoopMatching.MachineMain

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_SparseBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LoopMatching.supportedMatchingFintype _root_.OAI.MatchingEntropy.LooplessGraph.incidentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching

theorem recordedVertices_card_le (G : Input) :
    (recordedVertices G).card ≤ 2 * G.ordinary.records.length + G.loops.length := by
  have h := List.toFinset_card_le (G.ordinary.records.map BinaryMatching.Record.left ++
    G.ordinary.records.map BinaryMatching.Record.right ++
    G.loops.map LoopRecord.vertex)
  simpa only [recordedVertices, List.length_append, List.length_map, two_mul] using h

theorem ordinary_endpoints_mem_recordedVertices (G : Input)
    (e : BinaryMatching.Pair G.n) (he : BinaryMatching.multiplicity G.ordinary e ≠ 0) :
    e.val.1.val ∈ recordedVertices G ∧ e.val.2.val ∈ recordedVertices G := by
  unfold BinaryMatching.multiplicity at he
  cases hf : G.ordinary.records.find?
      (fun r => r.left = e.val.1.val && r.right = e.val.2.val) with
  | none => simp only [hf] at he; exact (he rfl).elim
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    constructor
    · have hm : e.val.1.val ∈ G.ordinary.records.map BinaryMatching.Record.left :=
        List.mem_map.mpr ⟨r, hr, hp.1⟩
      simp only [recordedVertices, List.mem_toFinset, List.mem_append]
      exact Or.inl (Or.inl hm)
    · have hm : e.val.2.val ∈ G.ordinary.records.map BinaryMatching.Record.right :=
        List.mem_map.mpr ⟨r, hr, hp.2⟩
      simp only [recordedVertices, List.mem_toFinset, List.mem_append]
      exact Or.inl (Or.inr hm)

theorem loop_mem_recordedVertices (G : Input) (v : Fin G.n)
    (hv : loopMultiplicity G v ≠ 0) : v.val ∈ recordedVertices G := by
  unfold loopMultiplicity at hv
  cases hf : G.loops.find? (fun r => r.vertex == v.val) with
  | none => simp only [hf] at hv; exact (hv rfl).elim
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have heq : r.vertex = v.val := by simpa using hp
    have hm : v.val ∈ G.loops.map LoopRecord.vertex := List.mem_map.mpr ⟨r, hr, heq⟩
    simp only [recordedVertices, List.mem_toFinset, List.mem_append]
    exact Or.inr hm

theorem range_subset_recordedVertices_of_weight_ne_zero (G : Input)
    (M : PartialMatching G.n) (hM : weight G M ≠ 0) :
    Finset.range G.n ⊆ recordedVertices G := by
  classical
  intro x hx
  let v : Fin G.n := ⟨x, Finset.mem_range.mp hx⟩
  by_cases hloop : v ∈ loopVertices M
  · have hn : loopMultiplicity G v ≠ 0 := by
      intro hz
      exact hM (weight_eq_zero_of_loopMultiplicity_eq_zero G M v hloop hz)
    exact loop_mem_recordedVertices G v hn
  · have hex : ∃ e ∈ M.val, (BinaryMatching.completeGraph G.n).Incident v e := by
      simpa only [loopVertices, Finset.mem_filter, Finset.mem_univ, true_and,
        not_forall, not_not, exists_prop] using hloop
    obtain ⟨e, he, hi⟩ := hex
    have hn : BinaryMatching.multiplicity G.ordinary e ≠ 0 := by
      intro hz
      exact hM (weight_eq_zero_of_multiplicity_eq_zero G M e he hz)
    have hep := ordinary_endpoints_mem_recordedVertices G e hn
    change e.val.1 = v ∨ e.val.2 = v at hi
    rcases hi with hi | hi
    · simpa only [hi] using hep.1
    · simpa only [hi] using hep.2

theorem vertex_bound_of_weight_ne_zero (G : Input) (M : PartialMatching G.n)
    (hM : weight G M ≠ 0) :
    G.n ≤ 2 * G.ordinary.records.length + G.loops.length := by
  have h := Finset.card_le_card (range_subset_recordedVertices_of_weight_ne_zero G M hM)
  rw [Finset.card_range] at h
  exact h.trans (recordedVertices_card_le G)

theorem count_eq_zero_of_sparse_bound (G : Input)
    (h : 2 * G.ordinary.records.length + G.loops.length < G.n) : count G = 0 := by
  apply count_eq_zero_of_forall_weight_eq_zero
  intro M
  by_contra hM
  exact (Nat.not_le_of_gt h) (vertex_bound_of_weight_ne_zero G M hM)

end LoopMatching

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching

theorem actual_algorithm_correct (G : Input) :
    0 < (MachineMain.A G).2 ∧
    (MachineMain.A G).1 ≤ (MachineMain.A G).2 * count G ∧
    (MachineMain.A G).2 * count G ≤ 2 ^ (18 * G.n) * (MachineMain.A G).1 ∧
    ((MachineMain.A G).1 = 0 ↔ count G = 0) := by
  by_cases h : 2 * G.ordinary.records.length + G.loops.length < G.n
  · have hz := count_eq_zero_of_sparse_bound G h
    simp [MachineMain.A, h, hz]
  · rw [MachineMain.A, ite_eq_right h]
    exact ⟨Approximation.output_den_pos G,
      Approximation.output_bounds_of_expanded_count G
        (fun j _ => expanded_count G j)⟩

theorem fullEndpoint_oai : FullEndpoint := by
  obtain ⟨machine, hfinite, hlength⟩ := MachineMain.computational_endpoint
  exact ⟨MachineMain.A, machine, hfinite, hlength, actual_algorithm_correct⟩

end LoopMatching

end OAI
end

theorem solution : type_of% @OAI.LoopMatching.fullEndpoint_oai := @OAI.LoopMatching.fullEndpoint_oai
