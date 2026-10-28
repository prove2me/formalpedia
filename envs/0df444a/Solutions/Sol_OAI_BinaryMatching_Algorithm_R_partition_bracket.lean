-- Prove2me | solution 1 for OAI.BinaryMatching.Algorithm.R_partition_bracket
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:06:11.750675+00:00
-- url     : https://prove2.me/submissions/5ab73cfa-eddd-4da8-8787-e88192a5e764

import Mathlib
import Definitions.Def_SingletonLoopMatching
import Definitions.Def_OAIW2LM004

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

theorem probabilitySimplex_le_one {Index : Type*} [Fintype Index] {weights : Index → ℝ}
    (mem : weights ∈ probabilitySimplex Index) (index : Index) : weights index ≤ 1 := by
  rw [← mem.2]
  exact Finset.single_le_sum (fun other _ ↦ mem.1 other) (Finset.mem_univ index)

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
theorem compact_feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) :
    IsCompact (G.feasibleLaws y) := by
  exact (isCompact_probabilitySimplex G.Matching).inter_right
    (isClosed_eq G.continuous_mean continuous_const)

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


section LinearHelper
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_le_of_ker_le (U : Submodule ℝ A) (f : A →ₗ[ℝ] B)
    (h : f.ker ≤ U) : finrank ℝ (A ⧸ U) ≤ finrank ℝ B := by
  have h1 := U.finrank_quotient_add_finrank
  have h2 := f.finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_mono h
  have h4 : finrank ℝ f.range ≤ finrank ℝ B := Submodule.finrank_le _
  omega

theorem quotient_finrank_le_pair (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U) :
    finrank ℝ (A ⧸ U) ≤ finrank ℝ (B ⧸ W)+finrank ℝ (C ⧸ Z) := by
  let F := (W.mkQ.comp f).prod (Z.mkQ.comp g)
  have hk : F.ker ≤ U := by
    intro u hu
    have hh : (W.mkQ (f u), Z.mkQ (g u))=0 := hu
    have hW : f u ∈ W := by
      have hq := congrArg Prod.fst hh
      simpa using hq
    have hZ : g u ∈ Z := by
      have hq := congrArg Prod.snd hh
      simpa using hq
    exact h u hW hZ
  simpa using quotient_finrank_le_of_ker_le U F hk

end LinearHelper
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

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_sub (G : LooplessGraph V E) (x y : E → ℝ) (S : Finset V) :
    G.cutMass (x-y) S = G.cutMass x S-G.cutMass y S := by
  have h := G.cutMass_linear x y 1 (-1) S
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
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Face
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Active face spaces, their codimension bounds, and local radial extension.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [DecidableEq E] in
 theorem faceCodimension_no_tight (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    G.faceCodimension x ≤ Fintype.card V := by
  classical
  let F := G.degreeLinear.comp (positiveExtension x)
  have hk : F.ker ≤ G.faceSpace x := by
    intro u hu
    have hd : G.degreeLinear (positiveExtension x u)=0 := hu
    refine ⟨hd,?_⟩
    exact G.trivial_tight_cut_preserved heven hnt _ (congrFun hd)
  simpa [faceCodimension] using quotient_finrank_le_of_ker_le (G.faceSpace x) F hk

omit [DecidableEq E] in
 theorem faceSpace_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope := by
  exact G.constraint_eventually_line hx _ (fun e he => positiveExtension_zero x u he)
    (congrFun hu.1) hu.2

omit [Fintype V] [DecidableEq E] in
 theorem faceSpace_of_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ}
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope) :
    u ∈ G.faceSpace x := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hu
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • positiveExtension x u ∈ G.constraintPolytope ∧
        x+(-t) • positiveExtension x u ∈ G.constraintPolytope) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  refine ⟨?_,?_⟩
  · ext v
    have he := G.degree_linear x (positiveExtension x u) 1 a v
    simp only [one_smul,one_mul,hx.2.1,ha.2.1] at he
    change G.degree (positiveExtension x u) v=0
    nlinarith
  · intro S hS ht
    have he := G.cutMass_linear x (positiveExtension x u) 1 a S
    have he' := G.cutMass_linear x (positiveExtension x u) 1 (-a) S
    simp only [one_smul,one_mul,ht] at he he'
    have hp := ha.2.2 S hS
    have hn := hna.2.2 S hS
    change G.cutMass (positiveExtension x u) S=0
    nlinarith


omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem sideMarginal_line (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0<x e} → ℝ) (t : ℝ) :
    G.sideMarginal (x+t • positiveExtension x u) S = G.sideMarginal x S +
      t • positiveExtension (G.sideMarginal x S) (G.sideRestriction x S u) := by
  rfl

/-- Pullbacks of both contraction face spaces preserve every original active cut,
including cuts crossing the chosen tight cut. This is the substantive coupling step. -/
theorem faceSpace_of_side_spaces (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1)
    {u : {e // 0<x e} → ℝ}
    (h1 : G.sideRestriction x S u ∈ (G.onSide S).faceSpace (G.sideMarginal x S))
    (h2 : G.sideRestriction x Sᶜ u ∈ (G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ)) :
    u ∈ G.faceSpace x := by
  have hc := odd_compl_of_even heven hS
  have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
  have hx1 := G.restriction_mem_constraints hx S hS ht
  have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
  have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
  have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
  apply G.faceSpace_of_eventually_line hx
  filter_upwards [(G.onSide S).faceSpace_eventually_line hx1 h1,
    (G.onSide Sᶜ).faceSpace_eventually_line hx2 h2] with t ht1 ht2
  rw [← G.sideMarginal_line x S u t] at ht1
  rw [← G.sideMarginal_line x Sᶜ u t] at ht2
  have hp1 : G.sideMarginal (x+t • positiveExtension x u) S ∈ (G.onSide S).polytope := by
    rwa [(G.onSide S).polytope_eq_constraints hv1]
  have hp2 : G.sideMarginal (x+t • positiveExtension x u) Sᶜ ∈ (G.onSide Sᶜ).polytope := by
    rwa [(G.onSide Sᶜ).polytope_eq_constraints hv2]
  obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hp1
  obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hp2
  have hp := (G.mem_polytope_iff _).mpr (G.couple_laws S _ hp hq (congrFun hpx) (congrFun hqx))
  exact G.polytope_subset_constraintPolytope hp

 theorem faceCodimension_le_sides (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1) :
    G.faceCodimension x ≤ (G.onSide S).faceCodimension (G.sideMarginal x S) +
      (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) := by
  classical
  exact quotient_finrank_le_pair (G.faceSpace x) ((G.onSide S).faceSpace (G.sideMarginal x S))
    ((G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ))
    (G.sideRestriction x S) (G.sideRestriction x Sᶜ)
    (fun _ => G.faceSpace_of_side_spaces heven hx S hS ht)

/-- Strong face-codimension induction for even orders at least four. -/
theorem faceCodimension_strong_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, G.faceCodimension x ≤ 2*(n-2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven hfour x hx
    have heven' : Even (Fintype.card W) := hcard ▸ heven
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
      have hn1 : 4≤Fintype.card (Option {v // v ∈ S}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hn2 : 4≤Fintype.card (Option {v // v ∈ Sᶜ}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hx1 := G.restriction_mem_constraints hx S hS ht
      have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
      have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
      have hb1 := ih _ hlt1 (G.onSide S) rfl hv1 hn1 _ hx1
      have hb2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 hn2 _ hx2
      have hb := G.faceCodimension_le_sides heven' hx S hS ht
      have hsum : Fintype.card (Option {v // v ∈ S}) + Fintype.card (Option {v // v ∈ Sᶜ})=n+2 := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hh := Finset.card_compl_add_card S
        omega
      change (G.onSide S).faceCodimension (G.sideMarginal x S) ≤ _ at hb1
      change (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) ≤ _ at hb2
      omega
    · have hb := G.faceCodimension_no_tight heven' hcut
      omega


omit [Fintype V] [DecidableEq E] in
 theorem degree_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (v : V) :
    G.degree (x+t • u) v=G.degree x v+t*G.degree u v := by
  simpa using G.degree_linear x u 1 t v

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (S : Finset V) :
    G.cutMass (x+t • u) S=G.cutMass x S+t*G.cutMass u S := by
  simpa using G.cutMass_linear x u 1 t S

omit [DecidableEq E] in
/-- Radial extension for this actual matching polytope. This is needed to prove
lower semicontinuity of the maximum entropy without assuming its regularity. -/
theorem constraint_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.constraintPolytope] x, x+t⁻¹ • (y-x) ∈ G.constraintPolytope := by
  have hn : ∀ᶠ y in 𝓝[G.constraintPolytope] x, ∀ e, 0≤(x+t⁻¹ • (y-x)) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      simpa [he] using mul_nonneg (inv_nonneg.mpr ht.le) (hy.1 e)
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun y : E → ℝ => (x+t⁻¹ • (y-x)) e) := by fun_prop
      have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 0<(x+t⁻¹ • (y-x)) e :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
      exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy => hy.le
  have hodd : ∀ᶠ y in 𝓝[G.constraintPolytope] x,
      ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t⁻¹ • (y-x)) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases hs : G.cutMass x S=1
      · filter_upwards [eventually_mem_nhdsWithin] with y hy _
        rw [cutMass_add_smul,cutMass_sub,hs]
        have hh := mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hy.2.2 S hS))
        linarith
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm hs)
        have hc : Continuous (fun y : E → ℝ => G.cutMass (x+t⁻¹ • (y-x)) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 1<G.cutMass (x+t⁻¹ • (y-x)) S :=
          (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
        exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy _ => hy.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd,eventually_mem_nhdsWithin] with y hn hodd hy
  refine ⟨hn,?_,hodd⟩
  intro v
  rw [degree_add_smul,degree_sub,hx.2.1,hy.2.1]
  ring

 theorem polytope_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.polytope] x, x+t⁻¹ • (y-x) ∈ G.polytope := by
  rw [G.polytope_eq_constraints heven] at hx ⊢
  exact G.constraint_eventually_expand hx ht

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



/-- Shannon entropy is the literal sum of negative probability-log-probability terms. -/
theorem entropy_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = -(∑ i, p i * Real.log (p i)) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib, neg_mul]

theorem continuous_entropy {ι : Type*} [Fintype ι] :
    Continuous (entropy : (ι → ℝ) → ℝ) := by
  unfold entropy
  fun_prop

theorem entropy_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (hp.1 i)
    (probabilitySimplex_le_one hp i)

/-- The entropy bound used in the counting reduction, including zero probabilities. -/
theorem entropy_le_log_card {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : entropy p ≤ Real.log (Fintype.card ι) := by
  have hn : 0 < Fintype.card ι := by
    by_contra h
    have hz : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos h
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hz
    simpa using hp.2
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    Real.negMulLog_le_one_sub_self (mul_nonneg hnR.le (hp.1 i)))
  simp_rw [Real.negMulLog_mul] at h
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hp.2, one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sub_self] at h
  change Real.negMulLog (Fintype.card ι) + (Fintype.card ι : ℝ) * entropy p ≤ 0 at h
  rw [Real.negMulLog] at h
  nlinarith

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem coordinate_mem_Icc (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) (e : E) : y e ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  constructor
  · exact Finset.sum_nonneg (fun M _ ↦ mul_nonneg (hp.1 M) (G.indicator_nonneg M e))
  · calc
      ∑ M, p M * G.indicator M e ≤ ∑ M, p M * 1 :=
        Finset.sum_le_sum (fun M _ ↦ mul_le_mul_of_nonneg_left (G.indicator_le_one M e) (hp.1 M))
      _ = 1 := by simpa using hp.2


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

theorem indicator_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) :
    ∑ e, G.indicator M e = (m : ℝ) := by
  simp [indicator, G.matching_card hV M]

/-- All feasible marginal vectors have mass m, as in the entropy proof. -/
theorem marginal_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) {y : E → ℝ} (hy : y ∈ G.polytope) :
    ∑ e, y e = (m : ℝ) := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  simp_rw [mean]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.indicator_sum hV]
  rw [← Finset.sum_mul, hp.2, one_mul]

end LooplessGraph

omit [Fintype V] [DecidableEq V] in
/-- The supremum in the definition of H is a genuine attained maximum. -/
theorem maxMatchingEntropy_attained (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    ∃ p ∈ G.feasibleLaws y, entropy p = maxMatchingEntropy G y := by
  have hc := (G.compact_feasibleLaws y).image continuous_entropy
  have hn := ((G.mem_polytope_iff y).mp hy).image entropy
  obtain ⟨p, hp, hpe⟩ := hc.sSup_mem hn
  exact ⟨p, hp, hpe⟩

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_nonneg (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) : 0 ≤ maxMatchingEntropy G y := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_nonneg hp.1

omit [Fintype V] [DecidableEq V] in
theorem entropy_le_maxMatchingEntropy (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y) :
    entropy p ≤ maxMatchingEntropy G y := by
  apply le_csSup
  · exact ((G.compact_feasibleLaws y).image continuous_entropy).bddAbove
  · exact ⟨p, hp, rfl⟩

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Optimizer
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Support and first-order identities for entropy-maximizing matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Concavity of actual finite-law Shannon entropy. -/
theorem entropy_mix_ge {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  unfold entropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
    (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)

/-- A zero probability gains a strict logarithmic bonus under mixing.
This is the boundary argument needed to obtain a positive entropy optimizer
on the entire face, not an assumed regularity of H. -/
theorem entropy_mix_zero_bonus {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {j : ι} (hj : p j = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q + q j * Real.negMulLog t ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  classical
  have hterm : ∀ i, (1-t) * Real.negMulLog (p i) + t * Real.negMulLog (q i) +
      (if i=j then q j * Real.negMulLog t else 0) ≤
        Real.negMulLog ((1-t)*p i+t*q i) := by
    intro i
    by_cases hi : i=j
    · subst i
      simp only [hj, Real.negMulLog_zero, mul_zero, zero_add, ite_true,
        Real.negMulLog_mul]
      linarith
    · simp only [hi, ↓reduceIte, add_zero]
      simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
        (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, entropy] using hh

/-- Every entropy maximizer on a convex feasible set has maximal support. -/
theorem entropy_maximizer_support {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      entropy (fun i => (1-t)*p i+t*q i) ≤ entropy p) {j : ι} (hjq : 0 < q j) :
    0 < p j := by
  by_contra hj
  have hj0 : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
  have hqp : entropy q ≤ entropy p := by simpa using hmax 1 (by constructor <;> norm_num)
  let c := (entropy p-entropy q)/(q j)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let t := Real.exp (-c)
  have htp : 0 < t := Real.exp_pos _
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htp.le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc.le)⟩
  have hbonus := (entropy_mix_zero_bonus hp hq hj0 ht).trans (hmax t ht)
  have hlog : Real.log t = -c := Real.log_exp _
  rw [Real.negMulLog, hlog] at hbonus
  have he : q j * c = entropy p-entropy q+q j := by
    dsimp [c]
    field_simp
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- The preceding support conclusion for the concrete matching-law optimizer. -/
theorem matching_optimizer_support (G : LooplessGraph V E) {y : E → ℝ}
    {p q : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hq : q ∈ G.feasibleLaws y) (hopt : entropy p = maxMatchingEntropy G y)
    {M : G.Matching} (hM : 0 < q M) : 0 < p M := by
  apply entropy_maximizer_support hp.1.1 hq.1.1 _ hM
  intro t ht
  apply le_trans (entropy_le_maxMatchingEntropy (G := G) (y := y) ?_) (le_of_eq hopt.symm)
  constructor
  · exact convex_probabilitySimplex _ hp.1 hq.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
  · calc
      G.mean (fun i => (1-t)*p i+t*q i) =
          (1-t) • G.mean p + t • G.mean q := by
        exact (G.meanLinear).map_add ((1-t) • p) (t • q) |>.trans (by
          rw [LinearMap.map_smul, LinearMap.map_smul]; rfl)
      _ = y := by rw [hp.2, hq.2]; ext e; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring


/-- Supporting-line inequality for -x log x, with no positivity assumption
on the comparison probability x. -/
theorem negMulLog_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x ≤ -x * Real.log y + y-x := by
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hx hy.le)) hy.le
  have he : Real.negMulLog x = -x * Real.log y + y * Real.negMulLog (x/y) := by
    calc
      Real.negMulLog x = Real.negMulLog (y * (x/y)) := by congr 1; field_simp
      _ = (x/y) * Real.negMulLog y + y * Real.negMulLog (x/y) := Real.negMulLog_mul _ _
      _ = _ := by unfold Real.negMulLog; field_simp
  rw [he]
  have hdiv : y * (x/y) = x := by field_simp
  nlinarith

/-- Gibbs' inequality on a finite set, with the exact support condition
needed on boundary faces. -/
theorem entropy_le_crossEntropy {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) :
    entropy q ≤ -∑ i, q i * Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤
      -(q i * Real.log (p i)) + p i-q i := by
    intro i
    by_cases hi : p i = 0
    · simp [hi, hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp.1 i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, hp.2, hq.2, add_sub_cancel_right, entropy] using hh

/-- Derivative of entropy along a line supported on the positive probabilities. -/
theorem entropy_line_hasDerivAt {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hsupp : ∀ i, p i = 0 → v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => p i+t*v i))
      (-∑ i, v i * Real.log (p i) - ∑ i, v i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (p i+t*v i))
      ((-Real.log (p i)-1)*v i) 0 := by
    intro i
    by_cases hi : p i = 0
    · simpa only [hi, hsupp i hi, mul_zero, add_zero, Real.negMulLog_zero] using
        (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : p i+(0 : ℝ)*v i ≠ 0 := by simpa using hi
      simpa only [zero_mul, add_zero, one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hp).comp 0
          (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (p i))
  have he : (∑ i, (-Real.log (p i)-1)*v i) =
      -∑ i, v i*Real.log (p i) - ∑ i, v i := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (p _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

omit [Fintype V] [DecidableEq V] in
/-- The log probabilities of the actual optimizer annihilate every feasible
mass/mean-preserving linear variation. No exponential representation assumed. -/
theorem matching_optimizer_log_annihilates (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y) (v : G.Matching → ℝ)
    (hvsum : ∑ M, v M = 0) (hvmean : G.mean v = 0)
    (hsupp : ∀ M, p M = 0 → v M = 0) :
    ∑ M, v M * Real.log (p M) = 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ M, 0 ≤ p M+t*v M := by
    apply Filter.eventually_all.mpr
    intro M
    by_cases hM : p M = 0
    · exact Filter.Eventually.of_forall (fun t => by simp [hM, hsupp M hM])
    · have hpos : 0 < p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hM)
      have hc : Continuous (fun t : ℝ => p M+t*v M) := by fun_prop
      have hh : {t : ℝ | 0 < p M+t*v M} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hpos)
      exact Filter.Eventually.mono hh (fun t ht => ht.le)
  have hlocal : IsLocalMax (fun t : ℝ => entropy (fun M => p M+t*v M)) 0 := by
    filter_upwards [hev] with t ht
    have hmean : G.mean (fun M => p M+t*v M) = y := by
      change G.meanLinear (p+t • v) = y
      rw [map_add, map_smul]
      change G.mean p + t • G.mean v = y
      rw [hp.2, hvmean, smul_zero, add_zero]
    have hsum : ∑ M, (p M+t*v M) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.1.2, hvsum, mul_zero, add_zero]
    have hle := entropy_le_maxMatchingEntropy (G := G) ⟨⟨ht, hsum⟩, hmean⟩
    simpa only [zero_mul, add_zero, ← hopt] using hle
  have hh := hlocal.deriv_eq_zero
  rw [(entropy_line_hasDerivAt p v hsupp).deriv, hvsum] at hh
  linarith


/-- A finite nonnegative vector permits small positive motion in any direction
which does not point outwards at its zero coordinates. -/
theorem exists_pos_nonneg_perturb {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, p i = 0 → 0 ≤ v i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ p i+t*v i := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, p i ≠ 0 → 0 ≤ p i+t*v i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : p i = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · have hc : Continuous (fun t : ℝ => p i+t*v i) := by fun_prop
      have hh : {t : ℝ | 0 < p i+t*v i} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using lt_of_le_of_ne (hp i) (Ne.symm hi))
      exact Filter.Eventually.mono hh (fun t ht _ => ht.le)
  have he' := (hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
  obtain ⟨t, ht, htp⟩ := he'.exists
  refine ⟨t, htp, fun i => ?_⟩
  by_cases hi : p i = 0
  · rw [hi, zero_add]
    exact mul_nonneg htp.le (hz i hi)
  · exact ht i hi

omit [Fintype V] [DecidableEq V] in
/-- The support of an optimizing law is a face: every law at a mean generated
by that support is itself supported there. This avoids assuming a face
representation of the marginal polytope in the entropy-optimization step. -/
theorem matching_optimizer_face_support (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {q r : G.Matching → ℝ} (hq : q ∈ probabilitySimplex G.Matching)
    (hr : r ∈ probabilitySimplex G.Matching) (hmean : G.mean q = G.mean r)
    (hrsupport : ∀ M, p M = 0 → r M = 0) :
    ∀ M, p M = 0 → q M = 0 := by
  obtain ⟨t, htp, ht⟩ := exists_pos_nonneg_perturb p (q-r) hp.1.1
    (fun M hM => by simpa [hrsupport M hM] using hq.1 M)
  have hsum : ∑ M, (p M+t*(q-r) M) = 1 := by
    simp only [Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hp.1.2, hq.2, hr.2]
    ring
  have hmean' : G.mean (fun M => p M+t*(q-r) M) = y := by
    change G.meanLinear (p+t • (q-r)) = y
    rw [map_add, map_smul, map_sub]
    change G.mean p + t • (G.mean q-G.mean r) = y
    rw [hp.2, hmean, sub_self, smul_zero, add_zero]
  intro M hM
  by_contra hqM
  have hqMp : 0 < q M := lt_of_le_of_ne (hq.1 M) (Ne.symm hqM)
  have hpM := matching_optimizer_support G hp ⟨⟨ht, hsum⟩, hmean'⟩ hopt
    (M := M) (by simpa [hM, hrsupport M hM] using mul_pos htp hqMp)
  simp [hM] at hpM

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Duality
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite exponential tilts, partition functions, and entropy duality on a face.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem partition_pos {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) : 0 < partition p a t := by
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hp.1 i)).mp
    (show 0 < ∑ i, p i by rw [hp.2]; norm_num)
  exact (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hp.1 i) (Real.exp_pos _).le)).mpr
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

theorem tiltedLaw_mem_simplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    tiltedLaw p a t ∈ probabilitySimplex ι := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hp.1 i) (Real.exp_pos _).le)
    (partition_pos hp a t).le, ?_⟩
  simp only [tiltedLaw, ← Finset.sum_div]
  exact div_self (partition_pos hp a t).ne'

/-- Gibbs' variational inequality for the explicit finite partition function,
including all boundary laws supported on p. -/
theorem entropy_partition_bound {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) (a : ι → ℝ) (t : ℝ) :
    entropy q ≤ Real.log (partition p a t) - ∑ i, q i*Real.log (p i) -
      t * ∑ i, q i*a i := by
  have hlog : ∀ i, q i * Real.log (tiltedLaw p a t i) =
      q i * Real.log (p i) + t*(q i*a i) - q i*Real.log (partition p a t) := by
    intro i
    by_cases hi : p i = 0
    · simp [hsupp i hi]
    · rw [tiltedLaw, Real.log_div (mul_ne_zero hi (Real.exp_ne_zero _))
        (partition_pos hp a t).ne', Real.log_mul hi (Real.exp_ne_zero _), Real.log_exp]
      ring
  calc
    entropy q ≤ -∑ i, q i*Real.log (tiltedLaw p a t i) :=
      entropy_le_crossEntropy (tiltedLaw_mem_simplex hp a t) hq (by
        intro i hi
        have hii : p i = 0 := by
          have := (div_eq_zero_iff).mp hi
          rcases this with hh | hh
          · exact (mul_eq_zero.mp hh).resolve_right (Real.exp_ne_zero _)
          · exact ((partition_pos hp a t).ne' hh).elim
        exact hsupp i hii)
    _ = _ := by
      simp_rw [hlog]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hq.2, one_mul]
      ring


omit [Fintype V] [DecidableEq V] in
theorem sum_mean_assoc (G : LooplessGraph V E) (p : G.Matching → ℝ) (u : E → ℝ) :
    (∑ M, p M * (∑ e, u e * G.indicator M e)) = ∑ e, u e * G.mean p e := by
  simp only [LooplessGraph.mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro M _
  ring

omit [Fintype V] [DecidableEq V] in
theorem linearScore_expectation (G : LooplessGraph V E) (p : G.Matching → ℝ)
    (u : E → ℝ) (c : ℝ) :
    (∑ M, p M * linearScore G u c M) =
      (∑ e, u e * G.mean p e) - c * ∑ M, p M := by
  simp only [linearScore, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_mean_assoc]
  ring

omit [Fintype V] [DecidableEq V] in
/-- A genuine upper bound on the actual maximum entropy at every mean in the
optimizer's face. This is proved from Gibbs' inequality, not assumed as a
replacement definition of H. -/
theorem matching_entropy_dual_bound (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {r : G.Matching → ℝ} (hr : r ∈ probabilitySimplex G.Matching)
    (hrsupport : ∀ M, p M = 0 → r M = 0)
    (u : E → ℝ) (c t : ℝ) :
    maxMatchingEntropy G (G.mean r) ≤
      Real.log (partition p (linearScore G u c) t) - ∑ M, r M * Real.log (p M) -
        t * ∑ M, r M * linearScore G u c M := by
  obtain ⟨q, hq, heq⟩ := maxMatchingEntropy_attained G (G.mean_mem_polytope hr)
  have hsuppq := matching_optimizer_face_support G hp hopt hq.1 hr hq.2 hrsupport
  have hmean : G.mean (q-r) = 0 := by
    change G.meanLinear (q-r) = 0
    rw [map_sub]
    change G.mean q-G.mean r = 0
    rw [hq.2, sub_self]
  have hsum : ∑ M, (q-r) M = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hq.1.2, hr.2, sub_self]
  have hlog := matching_optimizer_log_annihilates G hp hopt (q-r) hsum hmean
    (fun M hM => by simp [hsuppq M hM, hrsupport M hM])
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at hlog
  have hscore : (∑ M, q M*linearScore G u c M) = ∑ M, r M*linearScore G u c M := by
    rw [linearScore_expectation, linearScore_expectation, hq.2, hq.1.2, hr.2]
  rw [← heq]
  simpa only [hlog, hscore] using entropy_partition_bound hp.1 hq.1 hsuppq
    (linearScore G u c) t

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Calculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Derivatives of entropy and log-partition, and the nonlinear entropy barrier.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- First derivative of a finite exponential partition function. -/
theorem partition_hasDerivAt {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) :
    HasDerivAt (partition p a) (partition (fun i => p i*a i) a t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [one_mul, id_eq, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id t).mul_const (a i)).exp.const_mul (p i))

/-- The logarithmic partition derivative, with no infinite optimization
or interchange of limits: only finite sums. -/
theorem logPartition_hasDerivAt {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
  (partition_hasDerivAt p a t).log (partition_pos hp a t).ne'

/-- The second derivative of log-partition at the base law is variance. -/
theorem logPartition_second {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) :
    HasDerivAt (fun t => partition (fun i => p i*a i) a t / partition p a t)
      ((∑ i, p i*(a i)^2) - (∑ i, p i*a i)^2) 0 := by
  have hd := (partition_hasDerivAt (fun i => p i*a i) a 0).div
    (partition_hasDerivAt p a 0) (partition_pos hp a 0).ne'
  refine hd.congr_deriv ?_
  simp only [partition, zero_mul, Real.exp_zero, mul_one, hp.2, one_pow, div_one]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

theorem entropy_line_hasDerivAt_at {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (t : ℝ) (h : ∀ i, x i+t*v i ≠ 0 ∨ v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (x i+t*v i))
      ((-Real.log (x i+t*v i)-1)*v i) t := by
    intro i
    rcases h i with hi | hi
    · simpa only [one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hi).comp t
          (((hasDerivAt_id t).mul_const (v i)).const_add (x i))
    · simpa only [hi, mul_zero, add_zero] using (hasDerivAt_const t (Real.negMulLog (x i)))
  have he : (∑ i, (-Real.log (x i+t*v i)-1)*v i) = entropyLineD x v t := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (x _+t*v _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rfl
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

theorem entropyLineD_hasDerivAt {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    HasDerivAt (entropyLineD x v) (-∑ i, (v i)^2/x i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => v i*Real.log (x i+t*v i))
      ((v i)^2/x i) 0 := by
    intro i
    by_cases hi : x i = 0
    · simpa only [hi, hsupp i hi, zero_mul, zero_pow (by omega : 2 ≠ 0), zero_div] using
        (hasDerivAt_const (0:ℝ) (0:ℝ))
    · have hh := ((((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)).log
          (by simpa using hi)).const_mul (v i)
      simpa only [id_eq, one_mul, zero_mul, add_zero, pow_two, mul_div_assoc] using hh
  change HasDerivAt (fun t : ℝ => -(∑ i, v i*Real.log (x i+t*v i)) - ∑ i, v i)
    (-∑ i, (v i)^2/x i) 0
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)).neg.sub_const (∑ i, v i)



/-- A direct second-derivative calculation for the affine-law comparison
path used below. -/
theorem second_deriv_quadratic_adjustment {f fD g gD : ℝ → ℝ} {fDD gDD c₀ c₁ v : ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (fD t) t)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (gD t) t)
    (hfD : HasDerivAt fD fDD 0) (hgD : HasDerivAt gD gDD 0) :
    HasDerivAt (deriv (fun t => f t+c₀+t*c₁+t^2*v-g t))
      (fDD+2*v-gDD) 0 := by
  have hfirst : deriv (fun t => f t+c₀+t*c₁+t^2*v-g t) =ᶠ[𝓝 (0:ℝ)]
      (fun t => fD t+c₁+2*t*v-gD t) := by
    filter_upwards [hf, hg] with t hft hgt
    have hd := (((hft.add_const c₀).fun_add ((hasDerivAt_id t).mul_const c₁)).fun_add
      (((hasDerivAt_id t).fun_pow 2).mul_const v)).fun_sub hgt
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq, one_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using hd.deriv
  have hd := ((hfD.add_const c₁).fun_add
    (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const v)).fun_sub hgD
  have hd' : HasDerivAt (fun t => fD t+c₁+2*t*v-gD t) (fDD+2*v-gDD) 0 := by
    simpa only [Pi.add_apply, Pi.sub_apply, id_eq, mul_one] using hd
  exact hd'.congr_of_eventuallyEq hfirst


/-- The necessary one-dimensional second-derivative test, also when the
second derivative is defined by Lean's totalized derivative. -/
theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y h₁ h₂
    exact le_antisymm h₁ h₂
  have hh := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hh
  linarith


/-- All first derivatives on a neighborhood, including boundary coordinates
whose admissible direction is zero. -/
theorem entropy_line_eventually_hasDerivAt {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ≠ 0 ∨ v i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => Or.inr (hsupp i hi))
    · have hc : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
      have hn := hc.eventually_ne (show x i+(0:ℝ)*v i ≠ 0 by simpa using hi)
      exact hn.mono (fun t ht => Or.inl ht)
  exact hh.mono (fun t ht => entropy_line_hasDerivAt_at x v t ht)

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_SecondVariation
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The second-variation inequality at a maximum of the actual entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem score_law_eventually_simplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (hcenter : ∑ i, p i*a i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, (fun i => p i+t*(p i*a i)) ∈ probabilitySimplex ι := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < 1+t*a i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun t : ℝ => 1+t*a i) := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (by norm_num)
  filter_upwards [hh] with t ht
  constructor
  · intro i
    have h := mul_nonneg (hp.1 i) (ht i).le
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hcenter]
    ring

omit [Fintype V] [DecidableEq V] in
theorem mean_score_support (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ) :
    ∀ e, G.mean p e = 0 → G.mean (fun M => p M*a M) e = 0 := by
  intro e he
  have hterms : ∀ M, p M*G.indicator M e = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) => mul_nonneg (hp.1 M) (G.indicator_nonneg M e))).mp he
    exact fun M => hh M (Finset.mem_univ M)
  apply Finset.sum_eq_zero
  intro M _
  calc
    _ = a M*(p M*G.indicator M e) := by ring
    _ = 0 := by rw [hterms, mul_zero]

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Continuity
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Boundary lower semicontinuity of maximum entropy and attainment of the entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
/-- Concavity of H follows from mixing genuine optimizing probability laws. -/
theorem maxMatchingEntropy_mix_ge (G : LooplessGraph V E) {x y : E → ℝ}
    (hx : x ∈ G.polytope) (hy : y ∈ G.polytope) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t)*maxMatchingEntropy G x+t*maxMatchingEntropy G y ≤
      maxMatchingEntropy G ((1-t) • x+t • y) := by
  obtain ⟨p,hp,hpe⟩ := maxMatchingEntropy_attained G hx
  obtain ⟨q,hq,hqe⟩ := maxMatchingEntropy_attained G hy
  rw [← hpe,← hqe]
  apply (entropy_mix_ge hp.1.1 hq.1.1 ht).trans
  apply entropy_le_maxMatchingEntropy
  refine ⟨convex_probabilitySimplex _ hp.1 hq.1 (sub_nonneg.mpr ht.2) ht.1 (by ring),?_⟩
  change G.meanLinear ((1-t) • p+t • q) = _
  rw [map_add,map_smul,map_smul]
  change (1-t) • G.mean p+t • G.mean q = _
  rw [hp.2,hq.2]

/-- Boundary lower semicontinuity, using the finite matching-polytope constraints.
A fixed small mixing coefficient suffices for each prescribed entropy tolerance. -/
theorem maxMatchingEntropy_lowerSemicontinuousOn (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) :
    LowerSemicontinuousOn (maxMatchingEntropy G) G.polytope := by
  intro x hx r hr
  have hn := maxMatchingEntropy_nonneg G hx
  have hden : 0 < maxMatchingEntropy G x+1 := by linarith
  have ha : 0 < min (1:ℝ) ((maxMatchingEntropy G x-r)/(maxMatchingEntropy G x+1)) :=
    lt_min (by norm_num) (div_pos (sub_pos.mpr hr) hden)
  obtain ⟨t,ht0,htt⟩ := exists_between ha
  have ht1 : t<1 := htt.trans_le (min_le_left _ _)
  have htb : t*(maxMatchingEntropy G x+1) < maxMatchingEntropy G x-r :=
    (lt_div_iff₀ hden).mp (htt.trans_le (min_le_right _ _))
  filter_upwards [G.polytope_eventually_expand heven hx ht0] with y hy
  have hh := maxMatchingEntropy_mix_ge G hx hy ⟨ht0.le,ht1.le⟩
  have he : (1-t) • x+t • (x+t⁻¹ • (y-x))=y := by
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    field_simp
    ring
  rw [he] at hh
  have hz := mul_nonneg ht0.le (maxMatchingEntropy_nonneg G hy)
  nlinarith

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive semidefinite covariance matrices, rank, trace, and a spectral inequality.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_posSemidef (p : A → ℝ) (b : A → I → ℝ) :
    (covariance p b).PosSemidef := by
  simpa only [covariance, conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (weightedColumns p b)

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem covariance_entry {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) (i j : I) :
    covariance p b i j = ∑ a, p a*b a i*b a j := by
  unfold covariance
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedColumns, Matrix.transpose_apply]
  calc
    _ = (Real.sqrt (p a))^2 * b a i * b a j := by ring
    _ = _ := by rw [Real.sq_sqrt (hp a)]

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_mulVec {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) (i : I) :
    (covariance p b *ᵥ u) i = ∑ a, p a*b a i*(b a ⬝ᵥ u) := by
  simp only [Matrix.mulVec, dotProduct, covariance_entry hp, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_quadratic {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) : u ⬝ᵥ (covariance p b *ᵥ u) = ∑ a, p a*(b a ⬝ᵥ u)^2 := by
  rw [dotProduct]
  simp_rw [covariance_mulVec hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ i, u i*(p a*b a i*(b a ⬝ᵥ u))) =
      (∑ i, b a i*u i)*(p a*(b a ⬝ᵥ u)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = p a*(b a ⬝ᵥ u)^2 := by rw [← dotProduct]; ring

omit [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem weightedColumns_span {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    Submodule.span ℝ (Set.range (weightedColumns p b).col) = weightedDirectionSpace p b := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    by_cases ha : 0 < p a
    · have hb : b a ∈ weightedDirectionSpace p b := Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩
      exact Submodule.smul_mem _ (Real.sqrt (p a)) hb
    · have hz := le_antisymm (le_of_not_gt ha) (hp a)
      have he : (weightedColumns p b).col a = 0 := by
        ext i
        simp [weightedColumns, Matrix.col, hz]
      rw [he]
      exact (weightedDirectionSpace p b).zero_mem
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    have hb : (weightedColumns p b).col a.val ∈
        Submodule.span ℝ (Set.range (weightedColumns p b).col) := Submodule.subset_span ⟨a.val,rfl⟩
    have hs : Real.sqrt (p a.val) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 a.property)
    have hh := Submodule.smul_mem _ (Real.sqrt (p a.val))⁻¹ hb
    have he : (Real.sqrt (p a.val))⁻¹ • (weightedColumns p b).col a.val = b a.val := by
      ext i
      change (Real.sqrt (p a.val))⁻¹ * (Real.sqrt (p a.val) * b a.val i) = _
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    rw [he] at hh
    exact hh

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_rank {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    (covariance p b).rank = Module.finrank ℝ (weightedDirectionSpace p b) := by
  rw [covariance, rank_self_mul_transpose, rank_eq_finrank_span_cols, weightedColumns_span hp]

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem normalizedCentered_variance {p : A → ℝ} (hp : ∑ a, p a = 1)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) (i : I) :
    ∑ a, p a*(normalizedCentered v x a i)^2 = 1-x i := by
  have heq : ∀ a, p a*(normalizedCentered v x a i)^2 =
      (p a*v a i-2*x i*(p a*v a i)+(x i)^2*p a)/x i := by
    intro a
    rw [normalizedCentered, div_pow, Real.sq_sqrt (hxp i).le, ← mul_div_assoc]
    congr 1
    calc
      _ = p a*(v a i)^2-2*x i*(p a*v a i)+(x i)^2*p a := by ring
      _ = _ := by rw [hv]
  simp_rw [heq]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hx, hp, mul_one]
  field_simp [ne_of_gt (hxp i)]
  ring

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_MatchingCovariance
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_average (G : LooplessGraph V E) {x y : E → ℝ}
    {q : G.Matching → ℝ} (hq : q ∈ G.feasibleLaws y) (e : {e // 0 < x e}) :
    (∑ M, q M*matchingNormalized G x M e)=(y e.val-x e.val)/Real.sqrt (x e.val) := by
  simp only [matchingNormalized,normalizedCentered,← mul_div_assoc,mul_sub,
    ← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,hq.1.2,one_mul]
  rw [show (∑ M, q M*G.indicator M e.val)=y e.val from congrFun hq.2 e.val]

omit [Fintype V] [DecidableEq V] in
/-- A feasible two-sided direction has a positive-side law supported on the
entropy optimizer at its midpoint. -/
theorem midpoint_law_support (G : LooplessGraph V E) {x v : E → ℝ} {a : ℝ}
    {p q r : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hq : q ∈ G.feasibleLaws (x+a • v))
    (hr : r ∈ G.feasibleLaws (x+(-a) • v)) :
    ∀ M, 0 < q M → 0 < p M := by
  let w : G.Matching → ℝ := (1/2:ℝ) • q+(1/2:ℝ) • r
  have hw : w ∈ G.feasibleLaws x := by
    refine ⟨convex_probabilitySimplex _ hq.1 hr.1 (by norm_num) (by norm_num) (by norm_num),?_⟩
    change G.meanLinear ((1/2:ℝ) • q+(1/2:ℝ) • r) = _
    rw [map_add,map_smul,map_smul]
    change (1/2:ℝ) • G.mean q+(1/2:ℝ) • G.mean r = _
    rw [hq.2,hr.2]
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  intro M hM
  apply matching_optimizer_support G hp hw hopt
  change 0 < (1/2:ℝ)*q M+(1/2:ℝ)*r M
  have hh := hr.1.1 M
  linarith

/-- Every active-face direction belongs to the optimizer's normalized covariance
span. No face support or dimension assertion is being supplied as a hypothesis. -/
theorem normalized_face_mem (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x)
    {u : {e // 0 < x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    (fun e => u e/Real.sqrt (x e.val)) ∈ weightedDirectionSpace p (matchingNormalized G x) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hev := G.faceSpace_eventually_line (G.polytope_subset_constraintPolytope hx) hu
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hev
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope ∧
      x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope) ∧ 0 < t :=
    ((hev.and hneg).filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  rw [← G.polytope_eq_constraints heven] at ha hna
  obtain ⟨q,hq⟩ := (G.mem_polytope_iff _).mp ha
  obtain ⟨r,hr⟩ := (G.mem_polytope_iff _).mp hna
  have hsupp := midpoint_law_support G hp hopt hq hr
  have hsum : (∑ M, q M • matchingNormalized G x M) ∈
      weightedDirectionSpace p (matchingNormalized G x) := by
    apply Submodule.sum_mem
    intro M _
    by_cases hM : 0 < p M
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨M,hM⟩,rfl⟩)
    · have hq0 : q M=0 := le_antisymm (le_of_not_gt fun hqM => hM (hsupp M hqM)) (hq.1.1 M)
      simp only [hq0,zero_smul]
      exact Submodule.zero_mem _
  have hin := Submodule.smul_mem _ a⁻¹ hsum
  have he : a⁻¹ • (∑ M, q M • matchingNormalized G x M) =
      (fun e => u e/Real.sqrt (x e.val)) := by
    ext e
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
    rw [matchingNormalized_average G hq]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,LooplessGraph.positiveExtension_pos]
    field_simp
    ring
  rwa [he] at hin


omit [DecidableEq E] in
theorem sum_positive_support (x f : E → ℝ) (hf : ∀ e, ¬ 0 < x e → f e=0) :
    (∑ e, f e) = ∑ e : {e // 0 < x e}, f e.val := by
  classical
  have hz : (∑ e : {e // ¬ 0 < x e}, f e.val)=0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  have hh := Fintype.sum_subtype_add_sum_subtype (fun e => 0 < x e) f
  rw [hz,add_zero] at hh
  exact hh.symm

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_score (G : LooplessGraph V E) (x : E → ℝ)
    (u : {e // 0 < x e} → ℝ) (M : G.Matching) :
    linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e) M =
      matchingNormalized G x M ⬝ᵥ u := by
  classical
  unfold linearScore
  rw [← Finset.sum_sub_distrib]
  rw [sum_positive_support x _ (fun e he => by simp [matchingScoreWeights,LooplessGraph.positiveExtension,he])]
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  simp only [matchingScoreWeights,LooplessGraph.positiveExtension_pos,matchingNormalized,normalizedCentered]
  ring

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_mulVec (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (u : {e // 0 < x e} → ℝ) (e : {e // 0 < x e}) :
    (covariance p (matchingNormalized G x) *ᵥ u) e =
      G.mean (fun M => p M * linearScore G (matchingScoreWeights x u)
        (∑ e, matchingScoreWeights x u e*x e) M) e.val / Real.sqrt (x e.val) := by
  let a := linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e)
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  calc
    _ = ∑ M, (p M*a M*G.indicator M e.val-x e.val*(p M*a M))/Real.sqrt (x e.val) := by
      rw [covariance_mulVec hp.1.1]
      apply Finset.sum_congr rfl
      intro M _
      rw [← matchingNormalized_score G x u M]
      change p M*((G.indicator M e.val-x e.val)/Real.sqrt (x e.val))*a M = _
      ring
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.mul_sum,hcenter,mul_zero,sub_zero]
      rfl

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_CutAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.CutAlgebra
open Finset UnitFlow
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

lemma cutCapacity_eq (c : V → V → ℕ) (S : Finset V) :
    cutCapacity c S = ∑ i, ∑ j, if cross S i j then c i j else 0 := by
  simp only [cutCapacity,cross,ite_and]
  simp [Finset.sum_ite_irrel]
  apply sum_congr rfl; intro i hi
  have hSc : Sᶜ = univ.filter (fun j => j∉S) := by ext j; simp
  rw [hSc,sum_filter]
  simp

lemma cut_compl (c : V → V → ℕ) (hc : ∀ i j, c i j=c j i) (S : Finset V) :
    cutCapacity c Sᶜ = cutCapacity c S := by
  rw [cutCapacity_eq,cutCapacity_eq,sum_comm]
  apply sum_congr rfl; intro i hi
  apply sum_congr rfl; intro j hj
  simp only [cross,mem_compl,not_not]
  rw [hc j i]
  by_cases his : i∈S <;> by_cases hjs : j∈S <;> simp [his,hjs]

lemma cut_submodular (c : V → V → ℕ) (S A : Finset V) :
    cutCapacity c (S∩A) + cutCapacity c (S∪A) ≤ cutCapacity c S + cutCapacity c A := by
  simp only [cutCapacity_eq,← sum_add_distrib]
  apply sum_le_sum; intro i hi
  apply sum_le_sum; intro j hj
  by_cases his : i∈S <;> by_cases hia : i∈A <;>
    by_cases hjs : j∈S <;> by_cases hja : j∈A <;>
    simp [cross,his,hia,hjs,hja]

omit [DecidableEq V] [Fintype W] in
lemma push_symm (c : V → V → ℕ) (hc : ∀ i j, c i j=c j i) (f : V → W) :
    ∀ i j, push c f i j=push c f j i := by
  intro i j
  by_cases hij : i=j
  · subst j; rfl
  simp only [push,ite_eq_right hij,ite_eq_right (Ne.symm hij)]
  rw [sum_comm]
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  rw [hc v u]
  simp only [and_comm]

lemma cut_push (c : V → V → ℕ) (f : V → W) (T : Finset W) :
    cutCapacity (push c f) T = cutCapacity c (lift f T) := by
  rw [cutCapacity_eq,cutCapacity_eq]
  have he : ∀ i j, (if cross T i j then push c f i j else 0) =
      ∑ u, ∑ v, if cross T (f u) (f v) ∧ f u=i ∧ f v=j then c u v else 0 := by
    intro i j
    by_cases hh : cross T i j
    · have hij : i≠j := by intro h; subst j; exact hh.2 hh.1
      simp only [ite_eq_left hh,push,ite_eq_right hij]
      apply sum_congr rfl; intro u hu
      apply sum_congr rfl; intro v hv
      by_cases hui : f u=i <;> by_cases hvj : f v=j <;> simp_all
    · simp only [ite_eq_right hh]
      symm
      apply sum_eq_zero; intro u hu
      apply sum_eq_zero; intro v hv
      by_cases hui : f u=i <;> by_cases hvj : f v=j <;> simp_all
  simp_rw [he]
  rw [sum_four_swap]
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  simp only [cross,mem_lift]
  by_cases hh : f u∈T ∧ f v∉T
  · simp only [hh,true_and]
    simp [ite_and,Finset.sum_ite_irrel,eq_comm]
  · simp [hh]

end BinaryMatching.CutAlgebra
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OddCutParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.OddCutParity
open Finset UnitFlow CutAlgebra TerminalMincut
variable {n : ℕ}

lemma odd_other (U A : Finset (Fin n)) (hU : Even U.card) (hA : OddSide U A) :
    OddSide U Aᶜ := by
  have hh := terminal_partition U A
  rw [Nat.even_iff] at hU
  change Odd (A∩U).card at hA
  change Odd (Aᶜ∩U).card
  rw [Nat.odd_iff] at hA ⊢
  omega

lemma odd_separates (U S : Finset (Fin n)) (hU : Even U.card) (hS : OddSide U S) :
    Separates U S := by
  have hc := odd_other U S hU hS
  have hp : 0<(S∩U).card := by have := Nat.odd_iff.mp hS; omega
  have hpc : 0<(Sᶜ∩U).card := by have := Nat.odd_iff.mp hc; omega
  obtain ⟨a,ha⟩ := card_pos.mp hp
  obtain ⟨z,hz⟩ := card_pos.mp hpc
  exact ⟨a,(mem_inter.mp ha).2,z,(mem_inter.mp hz).2,
    (mem_inter.mp ha).1,mem_compl.mp (mem_inter.mp hz).1⟩

lemma split_odd (U S A : Finset (Fin n)) (hS : OddSide U S)
    (hnot : ¬OddSide (A∩U) S) : OddSide (Aᶜ∩U) S := by
  have hh := terminal_partition (S∩U) A
  have h₁ : A∩(S∩U)=S∩(A∩U) := by ext v; simp; tauto
  have h₂ : Aᶜ∩(S∩U)=S∩(Aᶜ∩U) := by ext v; simp; tauto
  rw [h₁,h₂] at hh
  simp only [OddSide,Nat.odd_iff] at hS hnot ⊢
  omega

lemma lift_contract (A T : Finset (Fin n)) (r : Fin n) :
    lift (contractMap A r) T = if r∈T then (T∩A)∪Aᶜ else T∩A := by
  ext v
  by_cases hv : v∈A <;> by_cases hr : r∈T <;>
    simp [mem_lift,contractMap,hv,hr]

lemma lift_card (U A T : Finset (Fin n)) (r : Fin n) :
    (lift (contractMap A r) T∩U).card =
      (T∩(A∩U)).card + if r∈T then (Aᶜ∩U).card else 0 := by
  rw [lift_contract]
  split_ifs with hr
  · have hd : Disjoint ((T∩A)∩U) (Aᶜ∩U) := by
      apply disjoint_left.mpr
      intro v hv hw
      exact (mem_compl.mp (mem_inter.mp hw).1) (mem_inter.mp (mem_inter.mp hv).1).2
    rw [union_inter_distrib_right,card_union_of_disjoint hd]
    rw [inter_assoc]
  · simp only [inter_assoc,add_zero]

lemma odd_lift_iff (U A T : Finset (Fin n)) (r : Fin n)
    (he : Even (Aᶜ∩U).card) :
    OddSide U (lift (contractMap A r) T) ↔ OddSide (A∩U) T := by
  simp only [OddSide,lift_card,Nat.odd_iff]
  rw [Nat.even_iff] at he
  split_ifs <;> omega

lemma lift_of_subset (A T : Finset (Fin n)) (r : Fin n) (hr : r∉A) (hT : T⊆A) :
    lift (contractMap A r) T=T := by
  have hrt : r∉T := fun h => hr (hT h)
  rw [lift_contract,ite_eq_right hrt,inter_eq_left.mpr hT]

lemma cut_contract_subset (c : Fin n → Fin n → ℕ) (A T : Finset (Fin n))
    (r : Fin n) (hr : r∉A) (hT : T⊆A) :
    cutCapacity (push c (contractMap A r)) T=cutCapacity c T := by
  rw [cut_push,lift_of_subset A T r hr hT]

lemma odd_subset_iff (U A T : Finset (Fin n)) (hT : T⊆A) :
    OddSide (A∩U) T ↔ OddSide U T := by
  have hh : T∩(A∩U)=T∩U := by rw [←inter_assoc,inter_eq_left.mpr hT]
  rw [OddSide,OddSide,hh]

end BinaryMatching.OddCutParity
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OddCutUncross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.OddCutUncross
open Finset UnitFlow CutAlgebra TerminalMincut OddCutParity
variable {n : ℕ}

lemma separates_compl (U A : Finset (Fin n)) (hA : Separates U A) : Separates U Aᶜ := by
  obtain ⟨a,ha,z,hz,haa,hza⟩ := hA
  exact ⟨z,hz,a,ha,mem_compl.mpr hza,by simpa using haa⟩

lemma uncross_on_side (c : Fin n → Fin n → ℕ) (hc : ∀ i j, c i j=c j i)
    (U A S : Finset (Fin n)) (hsep : Separates U A) (heven : Even (A∩U).card)
    (hmin : ∀ T, Separates U T → cutCapacity c A ≤ cutCapacity c T)
    (hinside : OddSide (A∩U) S) :
    ∃ T, T⊆A ∧ OddSide U T ∧ cutCapacity c T ≤ cutCapacity c S := by
  obtain ⟨a,ha,b,hb,haa,hba⟩ := hsep
  have horient : ∃ S', OddSide (A∩U) S' ∧ cutCapacity c S'=cutCapacity c S ∧
      ∃ z∈U, z∉A ∧ z∉S' := by
    by_cases hex : ∃ z∈U, z∉A ∧ z∉S
    · exact ⟨S,hinside,rfl,hex⟩
    · have hbS : b∈S := by
        by_contra hh
        exact hex ⟨b,hb,hba,hh⟩
      exact ⟨Sᶜ,odd_other (A∩U) S heven hinside,cut_compl c hc S,
        b,hb,hba,by simpa using hbS⟩
  obtain ⟨S',hodd,hcap,z,hz,hza,hzs⟩ := horient
  have hunion : Separates U (S'∪A) :=
    ⟨a,ha,z,hz,mem_union_right _ haa,by simpa only [mem_union,not_or] using And.intro hzs hza⟩
  have hlow := hmin (S'∪A) hunion
  have hsub := cut_submodular c S' A
  refine ⟨S'∩A,inter_subset_right,?_,?_⟩
  · simpa only [OddSide,inter_assoc] using hodd
  · omega

end BinaryMatching.OddCutUncross
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OddMincut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.OddMincut
open Finset UnitFlow UnitMincut TerminalMincut CutAlgebra OddCutParity OddCutUncross
variable {n : ℕ}

lemma outside_some (A : Finset (Fin n)) (hA : Aᶜ.Nonempty) :
    ∃ r, outside A=some r ∧ r∉A := by
  obtain ⟨v,hv⟩ := hA
  have hv' : v∉A := mem_compl.mp hv
  cases he : outside A with
  | none =>
    have hh := List.find?_eq_none.mp he v (by simp)
    simp [hv'] at hh
  | some r =>
    have hh := List.find?_some (show (List.finRange n).find?
      (fun v => decide (v∉A))=some r from he)
    exact ⟨r,rfl,by simpa using hh⟩

lemma cheaper_le_left (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cutCapacity c (cheaper c S T) ≤ cutCapacity c S := by
  unfold cheaper; split_ifs <;> omega

lemma cheaper_le_right (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cutCapacity c (cheaper c S T) ≤ cutCapacity c T := by
  unfold cheaper; split_ifs <;> omega

lemma cheaper_odd (c : Fin n → Fin n → ℕ) (U S T : Finset (Fin n))
    (hS : OddSide U S) (hT : OddSide U T) : OddSide U (cheaper c S T) := by
  unfold cheaper; split_ifs <;> assumption

lemma recurse_correct (fuel : ℕ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ i j, c i j=c j i) (U : Finset (Fin n)) (he : Even U.card)
    (hU : 2≤U.card) (hbound : U.card≤fuel) :
    OddSide U (recurse fuel c U) ∧
      ∀ S, OddSide U S → cutCapacity c (recurse fuel c U) ≤ cutCapacity c S := by
  induction fuel generalizing c U with
  | zero => omega
  | succ k ih =>
    let A := terminalCut c U
    obtain ⟨hsep,hmin⟩ := terminalCut_correct c U hU
    change Separates U A at hsep
    change ∀ T, Separates U T → cutCapacity c A ≤ cutCapacity c T at hmin
    by_cases hodd : OddSide U A
    · have heq : recurse (k+1) c U=A := by
        rw [recurse]
        change (if OddSide U A then A else _)=A
        exact ite_eq_left hodd
      rw [heq]
      exact ⟨hodd,fun S hS => hmin S (odd_separates U S he hS)⟩
    · have heA : Even (A∩U).card := by
        simp only [OddSide,Nat.odd_iff] at hodd
        rw [Nat.even_iff]; omega
      have heB := even_other U A he heA
      obtain ⟨hposA,hposB⟩ := separate_cards U A hsep
      have hpart := terminal_partition U A
      have htwoA : 2≤(A∩U).card := by rw [Nat.even_iff] at heA; omega
      have htwoB : 2≤(Aᶜ∩U).card := by rw [Nat.even_iff] at heB; omega
      have hboundA : (A∩U).card≤k := by omega
      have hboundB : (Aᶜ∩U).card≤k := by omega
      have hnonA : A.Nonempty := by
        obtain ⟨v,hv⟩ := card_pos.mp hposA
        exact ⟨v,(mem_inter.mp hv).1⟩
      have hnonB : Aᶜ.Nonempty := by
        obtain ⟨v,hv⟩ := card_pos.mp hposB
        exact ⟨v,(mem_inter.mp hv).1⟩
      obtain ⟨r,hr,hrA⟩ := outside_some A hnonB
      obtain ⟨q,hq,hqB⟩ := outside_some Aᶜ (by simpa using hnonA)
      let f := contractMap A r
      let g := contractMap Aᶜ q
      let X := recurse k (push c f) (A∩U)
      let Y := recurse k (push c g) (Aᶜ∩U)
      obtain ⟨hX,minX⟩ := ih (push c f) (push_symm c hc f) (A∩U) heA htwoA hboundA
      obtain ⟨hY,minY⟩ := ih (push c g) (push_symm c hc g) (Aᶜ∩U) heB htwoB hboundB
      change OddSide (A∩U) X at hX
      change OddSide (Aᶜ∩U) Y at hY
      have hLX : OddSide U (lift f X) := (odd_lift_iff U A X r heB).2 hX
      have hLY : OddSide U (lift g Y) :=
        (odd_lift_iff U Aᶜ Y q (by simpa using heA)).2 hY
      have heq : recurse (k+1) c U=cheaper c (lift f X) (lift g Y) := by
        rw [recurse]
        change (if OddSide U A then A else _) = _
        rw [ite_eq_right hodd,hr,hq]
      rw [heq]
      refine ⟨cheaper_odd c U _ _ hLX hLY,?_⟩
      intro S hS
      by_cases hSA : OddSide (A∩U) S
      · obtain ⟨T,hTA,hT,hcap⟩ := uncross_on_side c hc U A S hsep heA hmin hSA
        have hchild := (odd_subset_iff U A T hTA).2 hT
        have hminT := minX T hchild
        change cutCapacity (push c f) X ≤ cutCapacity (push c f) T at hminT
        rw [cut_push] at hminT
        rw [show f=contractMap A r from rfl,cut_contract_subset c A T r hrA hTA] at hminT
        exact (cheaper_le_left c _ _).trans (hminT.trans hcap)
      · have hSB := split_odd U S A hS hSA
        have hminB : ∀ T, Separates U T → cutCapacity c Aᶜ ≤ cutCapacity c T := by
          simpa only [cut_compl c hc] using hmin
        obtain ⟨T,hTB,hT,hcap⟩ := uncross_on_side c hc U Aᶜ S
          (separates_compl U A hsep) heB hminB hSB
        have hchild := (odd_subset_iff U Aᶜ T hTB).2 hT
        have hminT := minY T hchild
        change cutCapacity (push c g) Y ≤ cutCapacity (push c g) T at hminT
        rw [cut_push] at hminT
        rw [show g=contractMap Aᶜ q from rfl,cut_contract_subset c Aᶜ T q hqB hTB] at hminT
        exact (cheaper_le_right c _ _).trans (hminT.trans hcap)

 theorem oddCut_correct (c : Fin n → Fin n → ℕ) (hc : ∀ i j, c i j=c j i)
    (U : Finset (Fin n)) (he : Even U.card) (hU : 2≤U.card) :
    OddSide U (oddCut c U) ∧
      ∀ S, OddSide U S → cutCapacity c (oddCut c U) ≤ cutCapacity c S :=
  recurse_correct U.card c hc U he hU le_rfl

end BinaryMatching.OddMincut
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_DyadicEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma pieces_nonempty (k : ℕ) : pieces k ≠ [] := by simp [pieces]

lemma selectedPiece_mem_argmin (k : ℕ) (t : ℚ) :
    selectedPiece k t ∈ (pieces k).argmin (fun p => p.eval t) := by
  unfold selectedPiece
  cases he : (pieces k).argmin (fun p => p.eval t) with
  | none => exact (pieces_nonempty k (List.argmin_eq_none.mp he)).elim
  | some p => simp

lemma selectedReal_mem_argmin (k : ℕ) (t : ℝ) :
    selectedReal k t ∈ (pieces k).argmin (fun p => p.evalReal t) := by
  classical
  unfold selectedReal
  cases he : (pieces k).argmin (fun p => p.evalReal t) with
  | none => exact (pieces_nonempty k (List.argmin_eq_none.mp he)).elim
  | some p => simp

lemma psiReal_le_piece (k : ℕ) (t : ℝ) (p : Piece) (hp : p∈pieces k) :
    psiReal k t ≤ p.evalReal t :=
  List.le_of_mem_argmin hp (selectedReal_mem_argmin k t)

lemma le_psiReal (k : ℕ) (t b : ℝ) (h : ∀ p∈pieces k,b≤p.evalReal t) :
    b ≤ psiReal k t := h _ (List.argmin_mem (selectedReal_mem_argmin k t))

lemma realPsi_cast (k : ℕ) (t : ℚ) : psiReal k (t:ℝ)=(psi k t:ℝ) := by
  have cast_eval (p : Piece) : p.evalReal (t:ℝ)=(p.eval t:ℝ) := by
    simp [Piece.eval,Piece.evalReal]
  apply le_antisymm
  · have h := psiReal_le_piece k (t:ℝ) _ (List.argmin_mem (selectedPiece_mem_argmin k t))
    simpa only [cast_eval,psi] using h
  · apply le_psiReal
    intro p hp
    rw [cast_eval]
    exact_mod_cast (List.le_of_mem_argmin hp (selectedPiece_mem_argmin k t))

lemma psiReal_concave (k : ℕ) : ConcaveOn ℝ Set.univ (psiReal k) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  apply le_psiReal
  intro p hp
  have hx := psiReal_le_piece k x p hp
  have hy := psiReal_le_piece k y p hp
  simp only [smul_eq_mul]
  calc
    a*psiReal k x+b*psiReal k y ≤ a*p.evalReal x+b*p.evalReal y := by gcongr
    _ = p.evalReal (a*x+b*y) := by
      simp only [Piece.evalReal]
      have hh := congrArg (fun t => t*(p.constant:ℝ)) hab
      nlinarith [hh]

lemma first_mem_pieces (k : ℕ) : (⟨k,0⟩:Piece)∈pieces k := (mem_pieces k _).2 (Or.inl rfl)
lemma chord_mem_pieces (k j : ℕ) (hj : j<k) :
    (⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩:Piece)∈pieces k := (mem_pieces k _).2 (Or.inr ⟨j,hj,rfl⟩)

lemma chord_eval (j : ℕ) (t : ℝ) :
    (⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩:Piece).evalReal t=((j:ℝ)-1)*t+dyadic j := by
  simp [Piece.evalReal,dyadic]

lemma first_eval (k : ℕ) (t : ℝ) : (⟨k,0⟩:Piece).evalReal t=(k:ℝ)*t := by
  simp [Piece.evalReal]

lemma dyadic_pos (j : ℕ) : 0<dyadic j := by unfold dyadic; positivity
lemma dyadic_nonneg (j : ℕ) : 0≤dyadic j := (dyadic_pos j).le
lemma dyadic_succ (j : ℕ) : dyadic (j+1)=dyadic j/2 := by simp [dyadic,pow_succ,div_eq_mul_inv]
lemma dyadic_zero : dyadic 0=1 := by simp [dyadic]
lemma dyadic_mul_pow (j : ℕ) : dyadic j*(2:ℝ)^j=1 := by
  rw [dyadic,←mul_pow]; norm_num

lemma dyadic_scale (j l : ℕ) (h : l≤j) : dyadic l=(2:ℝ)^(j-l)*dyadic j := by
  have hj : j=l+(j-l) := by omega
  conv_rhs => rw [hj,dyadic,pow_add]
  rw [Nat.add_sub_cancel_left]
  change (2:ℝ)⁻¹^l=(2:ℝ)^(j-l)*((2:ℝ)⁻¹^l*(2:ℝ)⁻¹^(j-l))
  calc
    _ = (2:ℝ)⁻¹^l*1 := (mul_one _).symm
    _ = _ := by rw [←dyadic_mul_pow (j-l)]; unfold dyadic; ring

lemma chord_above_knot (l j : ℕ) :
    (j:ℝ)*dyadic j ≤ ((l:ℝ)-1)*dyadic j+dyadic l := by
  rcases lt_trichotomy l j with h|h|h
  · have hp : 1+(j-l:ℕ) ≤ (2:ℕ)^(j-l) := by
      have hh := one_add_mul_le_pow (show (-2:ℝ)≤1 by norm_num) (j-l)
      norm_num at hh
      exact_mod_cast hh
    have hpR : (1:ℝ)+(j:ℝ)-(l:ℝ) ≤ (2:ℝ)^(j-l) := by
      have := Nat.cast_le (α:=ℝ).mpr hp
      push_cast [Nat.cast_sub h.le] at this
      linarith
    rw [dyadic_scale j l h.le]
    nlinarith [mul_le_mul_of_nonneg_right hpR (dyadic_nonneg j)]
  · subst l; ring_nf; rfl
  · have hh : (j:ℝ)+1≤l := by exact_mod_cast h
    nlinarith [dyadic_nonneg j,dyadic_nonneg l]

lemma psiReal_knot (k j : ℕ) (hj : j≤k) : psiReal k (dyadic j)=(j:ℝ)*dyadic j := by
  apply le_antisymm
  · rcases lt_or_eq_of_le hj with h|h
    · have hh := psiReal_le_piece k (dyadic j) _ (chord_mem_pieces k j h)
      rw [chord_eval] at hh
      nlinarith
    · subst j
      simpa only [first_eval] using psiReal_le_piece k (dyadic k) _ (first_mem_pieces k)
  · apply le_psiReal
    intro p hp
    rcases (mem_pieces k p).1 hp with rfl|⟨l,_,rfl⟩
    · rw [first_eval]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (dyadic_nonneg j)
    · rw [chord_eval]; exact chord_above_knot l j

lemma psiReal_zero (k : ℕ) : psiReal k 0=0 := by
  apply le_antisymm
  · simpa only [first_eval,mul_zero] using psiReal_le_piece k 0 _ (first_mem_pieces k)
  · apply le_psiReal
    intro p hp
    rcases (mem_pieces k p).1 hp with rfl|⟨j,_,rfl⟩
    · simp [first_eval]
    · simpa only [chord_eval,mul_zero,zero_add] using dyadic_nonneg j

end
end BinaryMatching.Algorithm
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

lemma concave_affine_chord {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {l u t p c : ℝ} (hl : l∈S) (hu : u∈S) (hlu : l<u) (ht : t∈Set.Icc l u)
    (hfl : f l=p*l+c) (hfu : f u=p*u+c) : p*t+c≤f t := by
  let b := (t-l)/(u-l)
  have hd : 0<u-l := sub_pos.mpr hlu
  have hb : 0≤b := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hb1 : b≤1 := (div_le_one hd).2 (by linarith [ht.2])
  have he : (1-b)*l+b*u=t := by dsimp [b]; field_simp; ring
  have hc := hf.2 hl hu (sub_nonneg.mpr hb1) hb (sub_add_cancel 1 b)
  simp only [smul_eq_mul] at hc
  rw [he,hfl,hfu] at hc
  calc
    p*t+c=(1-b)*(p*l+c)+b*(p*u+c) := by rw [←he]; ring
    _ ≤ f t := hc

lemma psiReal_on_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    psiReal k t=(k:ℝ)*t := by
  apply le_antisymm
  · simpa only [first_eval] using psiReal_le_piece k t _ (first_mem_pieces k)
  · simpa only [add_zero] using concave_affine_chord (psiReal_concave k)
      (Set.mem_univ 0) (Set.mem_univ (dyadic k)) (dyadic_pos k) ht
      (p:=(k:ℝ)) (c:=0) (by simp [psiReal_zero]) (by rw [psiReal_knot k k le_rfl]; ring)

lemma psiReal_on_chord (k j : ℕ) (hj : j<k) {t : ℝ}
    (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    psiReal k t=((j:ℝ)-1)*t+dyadic j := by
  apply le_antisymm
  · simpa only [chord_eval] using psiReal_le_piece k t _ (chord_mem_pieces k j hj)
  · apply concave_affine_chord (psiReal_concave k) (Set.mem_univ _) (Set.mem_univ _)
      (show dyadic (j+1)<dyadic j by rw [dyadic_succ]; linarith [dyadic_pos j]) ht
    · rw [psiReal_knot k (j+1) hj,dyadic_succ,Nat.cast_add,Nat.cast_one]; ring
    · rw [psiReal_knot k j hj.le]; ring

lemma dyadic_cover (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    t≤dyadic k ∨ ∃ j<k,t∈Set.Icc (dyadic (j+1)) (dyadic j) := by
  induction k with
  | zero => exact Or.inl (by simpa only [dyadic_zero] using ht.2)
  | succ k ih =>
    by_cases h : t≤dyadic (k+1)
    · exact Or.inl h
    · right
      rcases ih with h'|⟨j,hj,hjt⟩
      · exact ⟨k,Nat.lt_succ_self k,le_of_not_ge h,h'⟩
      · exact ⟨j,Nat.lt_succ_of_lt hj,hjt⟩

lemma log_two_pos : 0<Real.log 2 := Real.log_pos (by norm_num)
lemma half_le_log_two : (1/2:ℝ)≤Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<2⁻¹ by norm_num)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

lemma log_dyadic (j : ℕ) : Real.log (dyadic j)=-(j:ℝ)*Real.log 2 := by
  simp [dyadic,Real.log_pow,Real.log_inv]

lemma phi_dyadic (j : ℕ) : phi (dyadic j)=(j:ℝ)*dyadic j := by
  simp only [phi,Real.negMulLog_def,log_dyadic]
  field_simp [log_two_pos.ne']

lemma phi_zero : phi 0=0 := by simp [phi]

lemma phi_concave : ConcaveOn ℝ (Set.Ici 0) phi := by
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := Real.concaveOn_negMulLog.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hd := div_le_div_of_nonneg_right hh log_two_pos.le
  simpa only [phi,add_div,mul_div_assoc] using hd

lemma phi_le_one {t : ℝ} (ht : t∈Set.Icc 0 1) : phi t≤1 := by
  have hp : (fun b : Bool => if b then t else 1-t) ∈ MatchingEntropy.probabilitySimplex Bool := by
    constructor
    · intro b; cases b <;> simp [ht.1,sub_nonneg.mpr ht.2]
    · simp
  have hh := MatchingEntropy.entropy_le_log_card hp
  simp only [MatchingEntropy.entropy,Fintype.sum_bool,Fintype.card_bool,Bool.false_eq_true,
    ↓reduceIte,Nat.cast_ofNat] at hh
  have hn := Real.negMulLog_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1] : 1-t≤1)
  unfold phi
  apply (div_le_one log_two_pos).2
  linarith

lemma phi_mul (u v : ℝ) : phi (u*v)=v*phi u+u*phi v := by
  simp only [phi,Real.negMulLog_mul]; ring

lemma phi_lower_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    (k:ℝ)*t ≤ phi t := by
  simpa only [add_zero] using concave_affine_chord phi_concave
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (dyadic_nonneg k)) (dyadic_pos k) ht
    (p:=(k:ℝ)) (c:=0) (by simp [phi_zero]) (by rw [phi_dyadic]; ring)

lemma phi_lower_chord (j : ℕ) {t : ℝ} (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    ((j:ℝ)-1)*t+dyadic j≤phi t := by
  apply concave_affine_chord phi_concave (Set.mem_Ici.mpr (dyadic_nonneg _))
    (Set.mem_Ici.mpr (dyadic_nonneg _))
    (show dyadic (j+1)<dyadic j by rw [dyadic_succ]; linarith [dyadic_pos j]) ht
  · rw [phi_dyadic,dyadic_succ,Nat.cast_add,Nat.cast_one]; ring
  · rw [phi_dyadic]; ring

lemma phi_upper_chord (j : ℕ) {t : ℝ} (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    phi t≤((j:ℝ)+1)*t := by
  have ht0 : 0<t := (dyadic_pos _).trans_le ht.1
  have hh := Real.log_le_log (dyadic_pos (j+1)) ht.1
  rw [log_dyadic,Nat.cast_add,Nat.cast_one] at hh
  unfold phi
  apply (div_le_iff₀ log_two_pos).2
  rw [Real.negMulLog_def]
  nlinarith [mul_le_mul_of_nonneg_left hh ht0.le]

lemma phi_error_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    phi t-(k:ℝ)*t≤dyadic k := by
  let r := t/dyadic k
  have hr : r∈Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg ht.1 (dyadic_nonneg k),(div_le_one (dyadic_pos k)).2 ht.2⟩
  have he : dyadic k*r=t := by dsimp [r]; field_simp [ne_of_gt (dyadic_pos k)]
  have hh := phi_mul (dyadic k) r
  rw [he,phi_dyadic] at hh
  have hu := mul_le_mul_of_nonneg_left (phi_le_one hr) (dyadic_nonneg k)
  nlinarith [hh,he]

theorem dyadic_entropy_error (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    0≤phi t-psiReal k t ∧ phi t-psiReal k t≤t+dyadic k := by
  rcases dyadic_cover k ht with h|⟨j,hj,hjt⟩
  · rw [psiReal_on_first k ⟨ht.1,h⟩]
    exact ⟨sub_nonneg.mpr (phi_lower_first k ⟨ht.1,h⟩),
      (phi_error_first k ⟨ht.1,h⟩).trans (by linarith [ht.1])⟩
  · rw [psiReal_on_chord k j hj hjt]
    have hlo := phi_lower_chord j hjt
    have hhi := phi_upper_chord j hjt
    have hd := dyadic_nonneg k
    constructor <;> linarith [hjt.2]

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

lemma degree_vertex_add (d : Fin n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => d e.val.1+d e.val.2) v =
      ((n:ℝ)-2)*d v+∑ j,d j := by
  rw [degree_from_symm (fun i j => d i+d j) (fun _ _ => add_comm _ _),sum_skip]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
  ring

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
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
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

lemma degree_add (x z : Pair n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => x e+z e) v=
      (completeGraph n).degree x v+(completeGraph n).degree z v := by
  simpa only [one_smul,one_mul,Pi.add_def] using (completeGraph n).degree_linear x z 1 1 v

lemma cut_add (x z : Pair n → ℝ) (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => x e+z e) S=
      (completeGraph n).cutMass x S+(completeGraph n).cutMass z S := by
  simpa only [one_smul,one_mul,Pi.add_def] using (completeGraph n).cutMass_linear x z 1 1 S

lemma cut_bound {z : Pair n → ℝ} {b : ℝ} (hb : 0≤b) (hz : ∀ e, |z e|≤b)
    (S : Finset (Fin n)) : |(completeGraph n).cutMass z S|≤Fintype.card (Pair n)*b := by
  calc
    _ ≤ ∑ e∈(completeGraph n).cut S, |z e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e∈(completeGraph n).cut S, b := sum_le_sum (fun e _ => hz e)
    _ = ((completeGraph n).cut S).card*b := by simp
    _ ≤ Fintype.card (Pair n)*b := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) hb

lemma correction_degree (hn : 4≤n) (x : Pair n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => x e+degreeCorrection x e) v=1 := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have h2 : (n:ℝ)-2≠0 := by linarith
  have h1 : (n:ℝ)-1≠0 := by linarith
  let d := fun v => 1-(completeGraph n).degree x v
  rw [degree_add]
  have hc : degreeCorrection x = ((n:ℝ)-2)⁻¹ • (fun e : Pair n => d e.val.1+d e.val.2) +
      (-1:ℝ) • (fun _ => (∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))) := by
    funext e; simp only [degreeCorrection,d,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
  rw [hc,(completeGraph n).degree_linear,degree_vertex_add,degree_constant]
  dsimp [d]
  field_simp
  ring

lemma correction_bound (hn : 4≤n) {x : Pair n → ℝ} {w : ℝ} (hw : 0≤w)
    (hdeg : ∀ v, |(completeGraph n).degree x v-1|≤w) (e : Pair n) :
    |degreeCorrection x e|≤2*w := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have h2 : 0<(n:ℝ)-2 := by linarith
  have h1 : 0<(n:ℝ)-1 := by linarith
  let d := fun v => 1-(completeGraph n).degree x v
  have hd (v) : |d v|≤w := by dsimp [d]; rw [abs_sub_comm]; exact hdeg v
  have hsum : |∑ v,d v|≤(n:ℝ)*w := by
    calc
      _ ≤ ∑ v,|d v| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : Fin n,w := sum_le_sum (fun v _ => hd v)
      _ = _ := by simp
  have ha : |(d e.val.1+d e.val.2)/((n:ℝ)-2)|≤w := by
    rw [abs_div,abs_of_pos h2,div_le_iff₀ h2]
    have hh := abs_add_le (d e.val.1) (d e.val.2)
    nlinarith [hd e.val.1,hd e.val.2]
  have hb : |(∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))|≤w := by
    rw [abs_div,abs_of_pos (mul_pos h2 h1),div_le_iff₀ (mul_pos h2 h1)]
    have hp : (n:ℝ)≤((n:ℝ)-2)*((n:ℝ)-1) := by nlinarith
    exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_right hp hw])
  exact (abs_sub _ _).trans (by dsimp [degreeCorrection] at *; linarith [ha,hb])

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

theorem feasibility_repair (hn : 4≤n) (heven : Even n) {x : Pair n → ℝ}
    (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) {w : ℝ} (hw : 0≤w)
    (hdeg : ∀ v, |(completeGraph n).degree x v-1|≤w)
    (hcut : ∀ S : Finset (Fin n),Odd S.card → 1-w≤(completeGraph n).cutMass x S) :
    ∃ y∈(completeGraph n).polytope,∀ e,|y e-x e|≤(2+10*(n:ℝ)^2)*w := by
  let A : ℝ := 10*(n:ℝ)^2
  let c := degreeCorrection x
  let x' := fun e => x e+c e
  let t := min 1 (A*w)
  let y : Pair n → ℝ := (1-t) • x'+t • uniform n
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have hA : 0≤A := by dsimp [A]; positivity
  have ht : 0≤t := le_min (by norm_num) (mul_nonneg hA hw)
  have ht1 : t≤1 := min_le_left _ _
  have htw : t≤A*w := min_le_right _ _
  have hc := correction_bound hn hw hdeg
  have hx'd := correction_degree hn x
  have hx'lo (e) : -2*w≤x' e := by
    have hh := (abs_le.mp (hc e)).1
    dsimp [x',c]; linarith [(hx e).1]
  have hx'cut (S) (hS : Odd S.card) :
      1-(1+2*(Fintype.card (Pair n):ℝ))*w≤(completeGraph n).cutMass x' S := by
    have hh := (abs_le.mp (cut_bound (mul_nonneg (by norm_num) hw) hc S)).1
    dsimp [x',c]; rw [cut_add]
    linarith [hcut S hS]
  have hA1 : 2≤A/((n:ℝ)-1) := by
    apply (le_div_iff₀ (by linarith)).2
    dsimp [A]; nlinarith
  have hA2 : 1+2*(Fintype.card (Pair n):ℝ)≤A/2 := by
    have hq : (Fintype.card (Pair n):ℝ)≤(n:ℝ)^2 := by exact_mod_cast q_le_square (n:=n)
    dsimp [A]; nlinarith
  have hyd : ∀ v,(completeGraph n).degree y v=1 := by
    intro v; dsimp [y]; rw [LooplessGraph.degree_linear,hx'd,uniform_degree hn]; ring
  have hy : y∈(completeGraph n).polytope := by
    by_cases hbig : 1≤A*w
    · have htt : t=1 := min_eq_left hbig
      simpa only [y,htt,sub_self,zero_smul,one_smul,zero_add] using uniform_feasible hn heven
    · have htt : t=A*w := min_eq_right (le_of_not_ge hbig)
      rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)]
      refine ⟨?_,hyd,?_⟩
      · intro e
        have h0 := mul_le_mul_of_nonneg_left (hx'lo e) (sub_nonneg.mpr ht1)
        have h1 := mul_le_mul_of_nonneg_right hA1 hw
        change 0≤(1-t)*x' e+t*uniform n e
        unfold uniform
        rw [htt] at *
        simp only [div_eq_mul_inv] at h1 ⊢
        nlinarith [mul_nonneg ht hw]
      · intro S hS
        by_cases htr : TrivialCut S
        · rw [trivial_cut_degree hyd htr]
        · have h0 := mul_le_mul_of_nonneg_left (hx'cut S hS) (sub_nonneg.mpr ht1)
          have h1 := mul_le_mul_of_nonneg_left (uniform_nontrivial_cut heven hS htr) ht
          have h2 := mul_le_mul_of_nonneg_right hA2 hw
          dsimp [y]; rw [LooplessGraph.cutMass_linear]
          have hqw : 0≤(1+2*(Fintype.card (Pair n):ℝ))*w := by positivity
          rw [htt] at *
          nlinarith [mul_nonneg ht hqw]
  refine ⟨y,hy,fun e => ?_⟩
  have hu : |uniform n e-x e|≤1 := by
    rw [abs_le]; constructor <;> linarith [(uniform_box hn e).1,(uniform_box hn e).2,(hx e).1,(hx e).2]
  have he : y e-x e=(1-t)*c e+t*(uniform n e-x e) := by dsimp [y,x']; ring
  rw [he]
  calc
    _ ≤ |(1-t)*c e|+|t*(uniform n e-x e)| := abs_add_le _ _
    _ = (1-t)*|c e|+t*|uniform n e-x e| := by rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht]
    _ ≤ (1-t)*(2*w)+t*1 := add_le_add (mul_le_mul_of_nonneg_left (hc e) (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hu ht)
    _ ≤ (2+10*(n:ℝ)^2)*w := by dsimp [A] at htw; nlinarith [mul_nonneg ht hw]

end
end BinaryMatching
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Violation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

lemma maxRow_mem_argmax (x : Pair n → ℝ) :
    maxRow x ∈ (allRows n).argmax (fun r => r.evalReal x) := by
  classical
  unfold maxRow
  cases he : (allRows n).argmax (fun r => r.evalReal x) with
  | none => have hh := List.argmax_eq_none.mp he; simp [allRows] at hh
  | some r => simp

lemma row_le_violation (x : Pair n → ℝ) (r : Affine n) (hr : r∈allRows n) :
    r.evalReal x≤violation x := List.le_of_mem_argmax hr (maxRow_mem_argmax x)

lemma violation_le (x : Pair n → ℝ) (b : ℝ) (h : ∀ r∈allRows n,r.evalReal x≤b) :
    violation x≤b := h _ (List.argmax_mem (maxRow_mem_argmax x))

lemma mem_allRows (r : Affine n) : r∈allRows n ↔
    r=zeroRow ∨ (∃ v,r=degreeRow v true ∨ r=degreeRow v false) ∨
      ∃ S : Finset (Fin n),Odd S.card ∧ r=cutRow S := by
  simp only [allRows,List.mem_append,List.mem_cons,List.mem_flatMap,List.mem_finRange,
    true_and,List.mem_map,List.mem_filter,mem_toList,mem_univ]
  aesop

lemma zero_row_eval (x : Pair n → ℝ) : (zeroRow : Affine n).evalReal x=0 := by
  simp [Affine.evalReal,zeroRow]

lemma degree_row_eval_pos (x : Pair n → ℝ) (v : Fin n) :
    (degreeRow v true).evalReal x=(completeGraph n).degree x v-1 := by
  simp [Affine.evalReal,degreeRow,LooplessGraph.degree,LooplessGraph.Incident,completeGraph,
    ite_mul,sub_eq_add_neg]
  apply sum_congr rfl; intro e _; rfl

lemma degree_row_eval_neg (x : Pair n → ℝ) (v : Fin n) :
    (degreeRow v false).evalReal x=1-(completeGraph n).degree x v := by
  simp only [Affine.evalReal,degreeRow,Bool.false_eq_true,↓reduceIte,Int.cast_one,
    Int.cast_ite,Int.cast_neg,Int.cast_zero,ite_mul,neg_one_mul,zero_mul]
  have he : (∑ e : Pair n,if e.val.1=v ∨ e.val.2=v then -x e else 0)=
      -(completeGraph n).degree x v := by
    simp only [LooplessGraph.degree,LooplessGraph.Incident,completeGraph,←sum_neg_distrib]
    apply sum_congr rfl; intro e _; split_ifs <;> simp_all
  rw [he]; ring

lemma cut_row_eval (x : Pair n → ℝ) (S : Finset (Fin n)) :
    (cutRow S).evalReal x=1-(completeGraph n).cutMass x S := by
  have he (e : Pair n) : ((e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.2∈S ∧ e.val.1∉S)) ↔
      (completeGraph n).Crosses S e := by
    simp only [LooplessGraph.Crosses,completeGraph]; tauto
  simp only [Affine.evalReal,cutRow,he,Int.cast_ite,Int.cast_neg,Int.cast_one,
    Int.cast_zero,ite_mul,neg_one_mul,zero_mul]
  have hsum : (∑ e : Pair n,if (completeGraph n).Crosses S e then -x e else 0)=
      -(completeGraph n).cutMass x S := by
    simp only [LooplessGraph.cutMass,LooplessGraph.cut,sum_filter,←sum_neg_distrib]
    apply sum_congr rfl; intro e _; split_ifs <;> simp_all
  rw [hsum]; ring

lemma violation_nonneg (x : Pair n → ℝ) : 0≤violation x := by
  simpa only [zero_row_eval] using row_le_violation x zeroRow ((mem_allRows _).2 (Or.inl rfl))

lemma degree_violation (x : Pair n → ℝ) (v : Fin n) :
    |(completeGraph n).degree x v-1|≤violation x := by
  have hp := row_le_violation x (degreeRow v true)
    ((mem_allRows _).2 (Or.inr (Or.inl ⟨v,Or.inl rfl⟩)))
  have hm := row_le_violation x (degreeRow v false)
    ((mem_allRows _).2 (Or.inr (Or.inl ⟨v,Or.inr rfl⟩)))
  rw [degree_row_eval_pos] at hp; rw [degree_row_eval_neg] at hm
  exact abs_le.mpr ⟨by linarith,hp⟩

lemma cut_violation (x : Pair n → ℝ) (S : Finset (Fin n)) (hS : Odd S.card) :
    1-violation x≤(completeGraph n).cutMass x S := by
  have hh := row_le_violation x (cutRow S)
    ((mem_allRows _).2 (Or.inr (Or.inr ⟨S,hS,rfl⟩)))
  rw [cut_row_eval] at hh; linarith

lemma violation_feasible (heven : Even n) {x : Pair n → ℝ}
    (hx : x∈(completeGraph n).polytope) : violation x=0 := by
  rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)] at hx
  apply le_antisymm _ (violation_nonneg x)
  apply violation_le
  intro r hr
  rcases (mem_allRows r).1 hr with rfl|⟨v,rfl|rfl⟩|⟨S,hS,rfl⟩
  · rw [zero_row_eval]
  · rw [degree_row_eval_pos,hx.2.1]; norm_num
  · rw [degree_row_eval_neg,hx.2.1]; norm_num
  · rw [cut_row_eval]; linarith [hx.2.2 S hS]

lemma violation_repair (hn : 4≤n) (heven : Even n) (x : Pair n → ℝ)
    (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) : ∃ y∈(completeGraph n).polytope,
      ∀ e,|y e-x e|≤(2+10*(n:ℝ)^2)*violation x :=
  feasibility_repair hn heven hx (violation_nonneg x) (degree_violation x) (cut_violation x)

lemma row_difference (r : Affine n) (x z : Pair n → ℝ) :
    r.evalReal z=r.evalReal x+∑ e,(r.coeff e:ℝ)*(z e-x e) := by
  simp only [Affine.evalReal,mul_sub,sum_sub_distrib]; ring

lemma row_coeff_bound (r : Affine n) (hr : r∈allRows n) (e : Pair n) : |(r.coeff e:ℝ)|≤1 := by
  rcases (mem_allRows r).1 hr with rfl|⟨v,rfl|rfl⟩|⟨S,_,rfl⟩
  · simp [zeroRow]
  · simp only [degreeRow,↓reduceIte]; split_ifs <;> norm_num
  · simp only [degreeRow,Bool.false_eq_true,↓reduceIte]; split_ifs <;> norm_num
  · simp only [cutRow]; split_ifs <;> norm_num

lemma active_row_subgradient (x : Pair n → ℝ) (r : Affine n)
    (hr : r∈allRows n) (ha : r.evalReal x=violation x) (z : Pair n → ℝ) :
    violation x+∑ e,(r.coeff e:ℝ)*(z e-x e)≤violation z := by
  rw [←ha,←row_difference]
  exact row_le_violation z r hr

lemma eval_cast (a : Affine n) (x : Pair n → ℚ) :
    a.evalReal (fun e => (x e:ℝ))=(a.eval x:ℝ) := by
  simp [Affine.eval,Affine.evalReal]

lemma capacities_symm (a : Table n ℤ) (i j : Fin n) : capacities a i j=capacities a j i := by
  unfold capacities
  rcases lt_trichotomy i j with h|h|h
  · simp [h,not_lt_of_ge h.le]
  · subst j; rfl
  · simp [h,not_lt_of_ge h.le]

lemma capacities_pair (a : Table n ℤ) (e : Pair n) :
    capacities a e.val.1 e.val.2=(entry a e).toNat := by
  simp [capacities,e.property,entry]

lemma cut_coordinates (D : ℕ) (a : Table n ℤ) (ha : ∀ e,0≤entry a e)
    (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => (coordinates D a e:ℝ)) S=
      (UnitFlow.cutCapacity (capacities a) S:ℝ)/(D:ℝ) := by
  have hx : (fun e => (coordinates D a e:ℝ))=
      (fun e : Pair n => (capacities a e.val.1 e.val.2:ℝ)/(D:ℝ)) := by
    funext e
    simp only [coordinates,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,capacities_pair]
    have he : ((entry a e).toNat:ℝ)=((entry a e:ℤ):ℝ) := by exact_mod_cast Int.toNat_of_nonneg (ha e)
    rw [he]
  rw [hx,cut_from_symm (fun i j => (capacities a i j:ℝ)/(D:ℝ)) (fun i j => by rw [capacities_symm a i j])]
  simp only [UnitFlow.cutCapacity,Nat.cast_sum,sum_div]

lemma activeRows_nonempty (a : Table n ℤ) : activeRows a≠[] := by simp [activeRows]

lemma activeRow_mem_argmax (D : ℕ) (a : Table n ℤ) :
    activeRow D a∈(activeRows a).argmax (fun r => r.eval (coordinates D a)) := by
  unfold activeRow
  cases he : (activeRows a).argmax (fun r => r.eval (coordinates D a)) with
  | none => exact (activeRows_nonempty a (List.argmax_eq_none.mp he)).elim
  | some r => simp

lemma activeRow_correct (hn : 2≤n) (heven : Even n) {D : ℕ} (hD : 0<D)
    (a : Table n ℤ) (ha : ∀ e,0≤entry a e) :
    activeRow D a∈allRows n ∧
      (activeRow D a).evalReal (fun e => (coordinates D a e:ℝ))=
        violation (fun e => (coordinates D a e:ℝ)) := by
  let S₀ := OddMincut.oddCut (capacities a) univ
  have hh := OddMincut.oddCut_correct (capacities a) (capacities_symm a) univ
    (by simpa using heven) (by simpa using hn)
  have hodd : Odd S₀.card := by simpa [OddCutParity.OddSide] using hh.1
  have hmin (S : Finset (Fin n)) (hS : Odd S.card) :
      UnitFlow.cutCapacity (capacities a) S₀≤UnitFlow.cutCapacity (capacities a) S :=
    hh.2 S (by simpa [OddCutParity.OddSide] using hS)
  have hsub : ∀ r∈activeRows a,r∈allRows n := by
    intro r hr
    rcases (mem_activeRows a r).1 hr with h|h|h
    · exact (mem_allRows r).2 (Or.inl h)
    · exact (mem_allRows r).2 (Or.inr (Or.inl h))
    · exact (mem_allRows r).2 (Or.inr (Or.inr ⟨S₀,hodd,h⟩))
  have ham := List.argmax_mem (activeRow_mem_argmax D a)
  refine ⟨hsub _ ham,le_antisymm (row_le_violation _ _ (hsub _ ham)) ?_⟩
  apply violation_le
  intro r hr
  have hdom (r' : Affine n) (hr' : r'∈activeRows a) :
      r'.evalReal (fun e => (coordinates D a e:ℝ))≤
        (activeRow D a).evalReal (fun e => (coordinates D a e:ℝ)) := by
    simp only [eval_cast]
    exact_mod_cast List.le_of_mem_argmax hr' (activeRow_mem_argmax D a)
  rcases (mem_allRows r).1 hr with h|h|⟨S,hS,rfl⟩
  · exact hdom r ((mem_activeRows a r).2 (Or.inl h))
  · exact hdom r ((mem_activeRows a r).2 (Or.inr (Or.inl h)))
  · apply le_trans _ (hdom (cutRow S₀) ((mem_activeRows a _).2 (Or.inr (Or.inr rfl))))
    rw [cut_row_eval,cut_row_eval,cut_coordinates D a ha,cut_coordinates D a ha]
    have hd : (0:ℝ)≤D := (Nat.cast_pos.mpr hD).le
    have hle : (UnitFlow.cutCapacity (capacities a) S₀:ℝ)≤
        UnitFlow.cutCapacity (capacities a) S := by exact_mod_cast hmin S hS
    linarith [div_le_div_of_nonneg_right hle hd]

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_ObjectivePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma piece_supergradient (k : ℕ) (p : Piece) (hp : p∈pieces k) (x : ℝ)
    (ha : p.evalReal x=psiReal k x) (z : ℝ) :
    psiReal k z≤psiReal k x+(p.slope:ℝ)*(z-x) := by
  have hh := psiReal_le_piece k z p hp
  rw [←ha]
  calc
    _ ≤ p.evalReal z := hh
    _ = p.evalReal x+(p.slope:ℝ)*(z-x) := by unfold Piece.evalReal; ring

lemma selectedPiece_supergradient (k : ℕ) (x : ℚ) (z : ℝ) :
    psiReal k z≤psiReal k (x:ℝ)+(slope k x:ℝ)*(z-(x:ℝ)) := by
  apply piece_supergradient k (selectedPiece k x)
    (List.argmin_mem (selectedPiece_mem_argmin k x)) (x:ℝ) _ z
  rw [realPsi_cast]
  simp [Piece.evalReal,Piece.eval,psi]

lemma psiReal_abs_sub (k : ℕ) (x y : ℝ) : |psiReal k x-psiReal k y|≤k*|x-y| := by
  have h (a b : ℝ) : psiReal k a-psiReal k b≤k*|a-b| := by
    have hm := List.argmin_mem (selectedReal_mem_argmin k b)
    have hh := piece_supergradient k (selectedReal k b) hm b rfl a
    have hb := piece_slope_bound k _ hm
    have hab := le_abs_self ((selectedReal k b).slope*(a-b))
    rw [abs_mul] at hab
    have hu := mul_le_mul_of_nonneg_right hb (abs_nonneg (a-b))
    linarith
  rw [abs_le]
  have hx := h x y
  have hy := h y x
  rw [abs_sub_comm y x] at hy
  exact ⟨by linarith,hx⟩

lemma objective_lipschitz (G : Input) (x y : Pair G.n → ℝ) :
    |objective G x-objective G y|≤(K G.n+L G:ℝ)*∑ e,|x e-y e| := by
  unfold objective
  rw [←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum; intro e _
  have he : psiReal (K G.n) (x e)+(beta G e:ℝ)*x e-
      (psiReal (K G.n) (y e)+(beta G e:ℝ)*y e)=
      (psiReal (K G.n) (x e)-psiReal (K G.n) (y e))+(beta G e:ℝ)*(x e-y e) := by ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_right (beta_bound G e) (abs_nonneg (x e-y e))
  have hh := abs_add_le (psiReal (K G.n) (x e)-psiReal (K G.n) (y e)) ((beta G e:ℝ)*(x e-y e))
  rw [abs_mul] at hh
  linarith [psiReal_abs_sub (K G.n) (x e) (y e)]

lemma exact_penalty (G : Input) (hn : 4≤G.n) (heven : Even G.n)
    (x : Pair G.n → ℝ) (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) :
    ∃ y∈(completeGraph G.n).polytope,penalized G x≤objective G y := by
  obtain ⟨y,hy,hdist⟩ := violation_repair hn heven x hx
  refine ⟨y,hy,?_⟩
  have hsum : (∑ e,|x e-y e|)≤(q G.n:ℝ)*(2+10*(G.n:ℝ)^2)*violation x := by
    calc
      _ ≤ ∑ _e : Pair G.n,(2+10*(G.n:ℝ)^2)*violation x := by
        apply sum_le_sum; intro e _; rw [abs_sub_comm]; exact hdist e
      _ = _ := by simp [q,mul_assoc]
  have hh := objective_lipschitz G x y
  have hmul := mul_le_mul_of_nonneg_left hsum (show (0:ℝ)≤K G.n+L G by positivity)
  have hM : (M₀ G:ℝ)=(q G.n:ℝ)*(K G.n+L G)*(2+10*(G.n:ℝ)^2) := by
    simp [M₀,A₀]
  unfold penalized
  rw [hM]
  have hab := le_abs_self (objective G x-objective G y)
  nlinarith

lemma penalized_feasible (G : Input) (heven : Even G.n) {x : Pair G.n → ℝ}
    (hx : x∈(completeGraph G.n).polytope) : penalized G x=objective G x := by
  simp [penalized,violation_feasible heven hx]

lemma trialValue_cast (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    (trialValue G a r:ℝ)=objective G (fun e => (coordinates (D₀ G) a e:ℝ))-
        (M₀ G:ℝ)*r.evalReal (fun e => (coordinates (D₀ G) a e:ℝ)) := by
  simp [trialValue,objective,realPsi_cast,eval_cast]

lemma trialValue_correct (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) :
    (trialValue G a (activeRow (D₀ G) a):ℝ)=
      penalized G (fun e => (coordinates (D₀ G) a e:ℝ)) := by
  rw [trialValue_cast,(activeRow_correct hn heven hD a ha).2]
  rfl

lemma gradient_supergradient (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e)
    (z : Pair G.n → ℝ) :
    penalized G z≤penalized G (fun e => (coordinates (D₀ G) a e:ℝ))+
      ∑ e,(gradient G a (activeRow (D₀ G) a) e:ℝ)*(z e-(coordinates (D₀ G) a e:ℝ)) := by
  let x := fun e => (coordinates (D₀ G) a e:ℝ)
  let r := activeRow (D₀ G) a
  obtain ⟨hr,hract⟩ := activeRow_correct hn heven hD a ha
  have hrow := active_row_subgradient x r hr hract z
  have hf : objective G z≤objective G x+
      ∑ e,((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))*(z e-x e) := by
    rw [objective,objective,←sum_add_distrib]
    apply sum_le_sum; intro e _
    have hh := selectedPiece_supergradient (K G.n) (coordinates (D₀ G) a e) (z e)
    dsimp [x] at *; nlinarith
  have hm := mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤M₀ G by positivity)
  have hgrad : (∑ e,(gradient G a r e:ℝ)*(z e-x e))=
      (∑ e,((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))*(z e-x e))-
        (M₀ G:ℝ)*∑ e,(r.coeff e:ℝ)*(z e-x e) := by
    simp only [gradient,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,
      sub_mul,sum_sub_distrib,mul_assoc,mul_sum]
  change penalized G z≤penalized G x+∑ e,(gradient G a r e:ℝ)*(z e-x e)
  rw [hgrad]
  unfold penalized
  linarith

lemma gradient_bound (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) (e : Pair G.n) :
    |(gradient G a (activeRow (D₀ G) a) e:ℝ)|≤K G.n+L G+M₀ G := by
  have hrow := row_coeff_bound _ (activeRow_correct hn heven hD a ha).1 e
  have hs := piece_slope_bound (K G.n) _ (List.argmin_mem
    (selectedPiece_mem_argmin (K G.n) (coordinates (D₀ G) a e)))
  change |(slope (K G.n) (coordinates (D₀ G) a e):ℝ)|≤K G.n at hs
  have hm := mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤M₀ G by positivity)
  have hcast : (gradient G a (activeRow (D₀ G) a) e:ℝ)=
      (slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ)-
        (M₀ G:ℝ)*((activeRow (D₀ G) a).coeff e:ℝ) := by simp [gradient]
  rw [hcast]
  have hh := abs_sub ((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))
    ((M₀ G:ℝ)*((activeRow (D₀ G) a).coeff e:ℝ))
  rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤M₀ G by positivity)] at hh
  linarith [abs_add_le (slope (K G.n) (coordinates (D₀ G) a e):ℝ) (beta G e:ℝ),beta_bound G e]

lemma gradient_square_bound (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) :
    (∑ e,(gradient G a (activeRow (D₀ G) a) e:ℝ)^2)≤D₀ G := by
  calc
    _ ≤ ∑ _e : Pair G.n,(K G.n+L G+M₀ G:ℝ)^2 := by
      apply sum_le_sum; intro e _
      have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (gradient_bound G hn heven hD a ha e)
      simpa only [sq_abs] using hh
    _ = D₀ G := by simp [D₀,q]

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Ascent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma clip_sq_le {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) (t : ℝ) :
    (min 1 (max 0 t)-z)^2 ≤ (t-z)^2 := by
  by_cases ht : t ≤ 0
  · rw [max_eq_left ht, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ht hz.1, sq_nonneg t]
  · have ht0 : 0 ≤ t := le_of_not_ge ht
    rw [max_eq_right ht0]
    by_cases ht1 : 1 ≤ t
    · rw [min_eq_left ht1]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (show 0 ≤ t+1-2*z by linarith [hz.2])]
    · rw [min_eq_right (le_of_not_ge ht1)]

lemma coordinates_cast {n : ℕ} (D : ℕ) (a : Table n ℤ) (e : Pair n) :
    (coordinates D a e : ℝ) = (↑(entry a e) : ℝ)/(D:ℝ) := by
  simp [coordinates]

lemma point_box (G : Input) (hn : 2 ≤ G.n) (j : ℕ) (e : Pair G.n) :
    point G j e ∈ Set.Icc (0:ℝ) 1 := by
  have hD : (0:ℝ) < D₀ G := by exact_mod_cast D₀_pos G hn
  have ha := iterate_box G j e
  have ha' : (↑(entry (iterate G j).numerators e) : ℝ) ∈ Set.Icc (0:ℝ) (D₀ G) :=
    ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  rw [point, coordinates_cast]
  exact ⟨div_nonneg ha'.1 hD.le, (div_le_one hD).mpr ha'.2⟩

lemma point_zero (G : Input) (e : Pair G.n) : point G 0 e=0 := by
  simp [point, coordinates, iterate, initial, at_tabulate]

lemma point_succ (G : Input) (hn : 2 ≤ G.n) (j : ℕ) (e : Pair G.n) :
    point G (j+1) e = min 1 (max 0 (point G j e+
      (gradient G (iterate G j).numerators (activeRow (D₀ G) (iterate G j).numerators) e:ℝ)/(D₀ G:ℝ))) := by
  have hD : (0:ℝ) < D₀ G := by exact_mod_cast D₀_pos G hn
  simp only [point, iterate, step, coordinates_cast, update, at_toTable,
    Int.cast_min, Int.cast_max, Int.cast_natCast, Int.cast_zero, Int.cast_add]
  rw [← min_div_div_right hD.le, ← max_div_div_right hD.le]
  rw [div_self hD.ne', zero_div, add_div]

lemma sampledValue_correct (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) (j : ℕ) :
    (sampledValue G j:ℝ)=penalized G (point G j) :=
  trialValue_correct G hn heven (D₀_pos G hn) _ (fun e => (iterate_box G j e).1)

lemma best_spec (G : Input) (t : ℕ) :
    ∃ v : ℚ, (iterate G (t+1)).best=some v ∧
      (∃ j < t+1, sampledValue G j=v) ∧
      ∀ j < t+1, sampledValue G j≤v := by
  induction t with
  | zero =>
    refine ⟨sampledValue G 0, rfl, ⟨0, by omega, rfl⟩, ?_⟩
    intro j hj
    have : j=0 := by omega
    subst j; rfl
  | succ t ih =>
    obtain ⟨v, hv, ⟨i, hi, hiv⟩, hmax⟩ := ih
    refine ⟨max (sampledValue G (t+1)) v, ?_, ?_, ?_⟩
    · change some ((iterate G (t+1)).best.elim (sampledValue G (t+1))
        (max (sampledValue G (t+1)))) = _
      rw [hv]; rfl
    · by_cases h : v ≤ sampledValue G (t+1)
      · exact ⟨t+1, by omega, (max_eq_left h).symm⟩
      · exact ⟨i, by omega, hiv.trans (max_eq_right (le_of_not_ge h)).symm⟩
    · intro j hj
      by_cases h : j=t+1
      · subst j; exact le_max_left _ _
      · exact (hmax j (by omega)).trans (le_max_right _ _)

lemma squareDistance_nonneg {I : Type*} [Fintype I] (x z : I → ℝ) :
    0 ≤ squareDistance x z := sum_nonneg fun _e _ => sq_nonneg _

lemma squareDistance_zero_bound (G : Input) (z : Pair G.n → ℝ)
    (hz : ∀ e, z e∈Set.Icc (0:ℝ) 1) : squareDistance (point G 0) z ≤ q G.n := by
  calc
    _ ≤ ∑ _e : Pair G.n, (1:ℝ) := by
      apply sum_le_sum; intro e _
      rw [point_zero]; nlinarith [(hz e).1, (hz e).2]
    _ = _ := by simp [q]

lemma distance_step (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) (j : ℕ)
    (z : Pair G.n → ℝ) (hz : ∀ e,z e∈Set.Icc (0:ℝ) 1) :
    2*(penalized G z-penalized G (point G j)) ≤
      (D₀ G:ℝ)*(squareDistance (point G j) z-squareDistance (point G (j+1)) z)+1 := by
  let x := point G j
  let g := fun e => (gradient G (iterate G j).numerators
    (activeRow (D₀ G) (iterate G j).numerators) e:ℝ)
  let D : ℝ := D₀ G
  have hD : 0<D := by change 0<(D₀ G:ℝ); exact_mod_cast D₀_pos G hn
  have hs : squareDistance (point G (j+1)) z ≤ ∑ e,(x e+g e/D-z e)^2 := by
    apply sum_le_sum; intro e _
    rw [point_succ G hn]
    exact clip_sq_le (hz e) _
  have he : D*(∑ e,(x e+g e/D-z e)^2) = D*squareDistance x z+
      2*(∑ e,g e*(x e-z e))+(∑ e,(g e)^2)/D := by
    calc
      _ = ∑ e, (D*(x e-z e)^2+2*(g e*(x e-z e))+(g e)^2/D) := by
        rw [mul_sum]
        apply sum_congr rfl; intro e _
        field_simp; ring
      _ = _ := by simp only [sum_add_distrib, ← mul_sum, ← sum_div, squareDistance]
  have hb : (∑ e,(g e)^2)/D ≤ 1 := by
    apply (div_le_one hD).mpr
    exact gradient_square_bound G hn heven (D₀_pos G hn) _ (fun e => (iterate_box G j e).1)
  have hg := gradient_supergradient G hn heven (D₀_pos G hn) (iterate G j).numerators
    (fun e => (iterate_box G j e).1) z
  have hsign : (∑ e,g e*(x e-z e)) = -(∑ e,g e*(z e-x e)) := by
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro e _; ring
  change penalized G z ≤ penalized G x+∑ e,g e*(z e-x e) at hg
  have hh := mul_le_mul_of_nonneg_left hs hD.le
  rw [he, hsign] at hh
  change 2*(penalized G z-penalized G x) ≤ D*(squareDistance x z-squareDistance (point G (j+1)) z)+1
  linarith

lemma trial_max_bound (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) :
    ∃ v : ℚ, (iterate G (q G.n*D₀ G)).best=some v ∧
      (∃ j < q G.n*D₀ G, sampledValue G j=v) ∧
      ∀ z : Pair G.n → ℝ, (∀ e,z e∈Set.Icc (0:ℝ) 1) →
        penalized G z ≤ (v:ℝ)+1 := by
  let T := q G.n*D₀ G
  have hT : 0<T := Nat.mul_pos (q_pos hn) (D₀_pos G hn)
  obtain ⟨v,hv,hatt,hmax⟩ := best_spec G (T-1)
  have heT : T-1+1=T := by omega
  rw [heT] at hv hatt hmax
  refine ⟨v,hv,hatt,?_⟩
  intro z hz
  have htR : (0:ℝ)<T := by exact_mod_cast hT
  have hsteps := sum_le_sum (s := range T) (fun j _ => distance_step G hn heven j z hz)
  have hilower : (T:ℝ)*(2*(penalized G z-(v:ℝ))) ≤
      ∑ j∈range T,2*(penalized G z-penalized G (point G j)) := by
    calc
      _ = ∑ _j∈range T,2*(penalized G z-(v:ℝ)) := by simp
      _ ≤ _ := by
        apply sum_le_sum; intro j hj
        have hjv : (sampledValue G j:ℝ)≤(v:ℝ) := by
          exact_mod_cast hmax j (mem_range.mp hj)
        rw [sampledValue_correct G hn heven] at hjv
        linarith
  have htel : (∑ j∈range T, ((D₀ G:ℝ)*
      (squareDistance (point G j) z-squareDistance (point G (j+1)) z)+1)) =
      (D₀ G:ℝ)*(squareDistance (point G 0) z-squareDistance (point G T) z)+T := by
    rw [sum_add_distrib,←mul_sum,sum_range_sub']
    simp
  rw [htel] at hsteps
  have hend := squareDistance_nonneg (point G T) z
  have hstart := squareDistance_zero_bound G z hz
  have hD : (0:ℝ)<D₀ G := by exact_mod_cast D₀_pos G hn
  have he : (T:ℝ)=(q G.n:ℝ)*(D₀ G:ℝ) := by dsimp [T]; norm_cast
  have hdist : (D₀ G:ℝ)*(squareDistance (point G 0) z-squareDistance (point G T) z)≤T := by
    rw [he]; nlinarith
  nlinarith

theorem R_objective_bracket (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    (∃ y∈(completeGraph G.n).polytope,(R G:ℝ)≤objective G y) ∧
      ∀ z∈(completeGraph G.n).polytope,objective G z≤(R G:ℝ)+2 := by
  obtain ⟨v,hv,⟨j,_hj,hjv⟩,hbound⟩ := trial_max_bound G (by omega) heven
  have hR : (R G:ℝ)=(Int.floor (v:ℝ):ℝ) := by
    simp only [R,hv,Option.getD_some,Rat.floor_cast]
  have hfloor : (R G:ℝ)≤(v:ℝ) := by rw [hR]; exact Int.floor_le _
  have hvfloor : (v:ℝ)<(R G:ℝ)+1 := by rw [hR]; exact Int.lt_floor_add_one _
  constructor
  · obtain ⟨y,hy,hyval⟩ := exact_penalty G hn heven (point G j) (point_box G (by omega) j)
    refine ⟨y,hy,hfloor.trans ?_⟩
    rw [←hjv,sampledValue_correct G (by omega) heven]
    exact hyval
  · intro z hz
    have hh := hbound z ((completeGraph G.n).coordinate_mem_Icc hz)
    rw [penalized_feasible G heven hz] at hh
    linarith

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Separable
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators Topology
open Filter
namespace MatchingEntropy

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem continuous_separableLower : Continuous (separableLower (E := E)) := by
  exact continuous_entropy.sub (continuous_const.mul (continuous_entropy.comp (by fun_prop)))

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separable_line_eventually_hasDerivAt (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t => separableLower (fun e => x e+t*v e))
        (separableLineD x v t) t := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  filter_upwards [entropy_line_eventually_hasDerivAt x v hzero,
    entropy_line_eventually_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar]
    with t ht hb
  have he : (fun t => separableLower (fun e => x e+t*v e)) =
      (fun t => entropy (fun e => x e+t*v e) -
        3 * entropy (fun e => (1-x e)+t*(-v e))) := by
    funext t
    unfold separableLower
    congr 2
    congr 1
    funext e
    ring
  rw [he]
  exact ht.sub (hb.const_mul 3)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separableLineD_hasDerivAt (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    HasDerivAt (separableLineD x v)
      (-(∑ e, (v e)^2/x e) + 3*(∑ e, (v e)^2/(1-x e))) 0 := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  have hd := (entropyLineD_hasDerivAt x v hzero).sub
    ((entropyLineD_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar).const_mul 3)
  exact hd.congr_deriv (by simp only [neg_sq]; ring)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separable_second_variation {A : Type*} [Fintype A]
    (x v : E → ℝ) (hzero : ∀ e, x e=0 → v e=0) (hone : ∀ e, x e=1 → v e=0)
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (a : A → ℝ)
    (hcenter : ∑ i, p i*a i=0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => separableLower (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    -(∑ e, (v e)^2/x e) + 3*(∑ e, (v e)^2/(1-x e)) +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  have hf := separable_line_eventually_hasDerivAt x v hzero hone
  have hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
    Filter.Eventually.of_forall (logPartition_hasDerivAt hp a)
  have hd := second_deriv_quadratic_adjustment (c₀ := c₀) (c₁ := c₁)
    (v := ∑ i, p i*(a i)^2) hf hg (separableLineD_hasDerivAt x v hzero hone)
    (logPartition_second hp a)
  have hc : ContinuousAt (fun t => separableLower (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hf.self_of_nhds.continuousAt.add_const c₀
        · fun_prop
      · fun_prop
    · exact hg.self_of_nhds.continuousAt
  have hh := second_deriv_nonpos_of_local_max hlocal hc
  rw [hd.deriv, hcenter] at hh
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem mean_score_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ)
    (hcenter : ∑ M, p M*a M=0) :
    ∀ e, G.mean p e=1 → G.mean (fun M => p M*a M) e=0 := by
  intro e he
  have hz : ∑ M, p M*(1-G.indicator M e)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e=0
    rw [he, sub_self]
  have hterms : ∀ M, p M*(1-G.indicator M e)=0 := by
    exact fun M => (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) =>
        mul_nonneg (hp.1 M) (sub_nonneg.mpr (G.indicator_le_one M e)))).mp hz M (by simp)
  calc
    _ = ∑ M, p M*a M := by
      apply Finset.sum_congr rfl
      intro M _
      have hh := hterms M
      have hh' : a M*(p M*(1-G.indicator M e))=0 := by rw [hh, mul_zero]
      nlinarith [hh']
    _ = 0 := hcenter

omit [Fintype V] [DecidableEq V] in

theorem matching_separable_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M=0) :
    -(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      3*(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/(1-x e)) +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by
  let a := linearScore G u c
  let v := G.mean (fun M => p M*a M)
  let c₀ := ∑ M, p M*Real.log (p M)
  let c₁ := ∑ M, (p M*a M)*Real.log (p M)
  have hzero : ∀ e, x e=0 → v e=0 := by
    rw [← hp.2]
    exact mean_score_support G hp.1 a
  have hone : ∀ e, x e=1 → v e=0 := by
    rw [← hp.2]
    exact mean_score_one G hp.1 a hcenter
  apply separable_second_variation x v hzero hone hp.1 a hcenter c₀ c₁
  filter_upwards [score_law_eventually_simplex hp.1 a hcenter] with t ht
  let r := fun M => p M+t*(p M*a M)
  have hr : r ∈ probabilitySimplex G.Matching := ht
  have hrmean : G.mean r=fun e => x e+t*v e := by
    change G.meanLinear (p+t • (fun M => p M*a M)) = _
    rw [map_add, map_smul]
    change G.mean p+t • v = _
    rw [hp.2]
    rfl
  have hdual := matching_entropy_dual_bound G hp hopt hr
    (fun M hM => by dsimp [r]; simp [hM]) u c t
  have hscore : (∑ M, r M*a M)=t*(∑ M, p M*(a M)^2) := by
    dsimp [r]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcenter, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hlog : (∑ M, r M*Real.log (p M))=c₀+t*c₁ := by
    dsimp [r, c₀, c₁]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
  change maxMatchingEntropy G (G.mean r) ≤
    Real.log (partition p a t) - (∑ M, r M*Real.log (p M)) - t*(∑ M, r M*a M) at hdual
  rw [hlog, hscore] at hdual
  have hmaxr := hmax (G.mean r) (G.mean_mem_polytope hr)
  have hpart := partition_zero hp.1 a
  simp only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, hpart,
    Real.log_one, sub_zero]
  rw [← hopt, entropy_eq p] at hmaxr
  rw [← hrmean]
  dsimp only [c₀] at *
  nlinarith

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_WeightedSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators
open Matrix
namespace MatchingEntropy

theorem spectral_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} (hC : C.IsHermitian) (e : I) :
    C e e = ∑ i, hC.eigenvalues i * (hC.eigenvectorBasis i e)^2 := by
  have hh := congrArg (fun A : Matrix I I ℝ => A e e) hC.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hh
  simpa only [mul_apply, diagonal_apply, star_eq_conjTranspose, conjTranspose_apply,
    star_trivial, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.IsHermitian.eigenvectorUnitary_apply, pow_two, mul_comm, mul_left_comm,
    mul_assoc] using hh

theorem covariance_weighted_rank {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} (hC : C.PosSemidef) (w : I → ℝ)
    (hsecond : ∀ u : I → ℝ,
      u ⬝ᵥ (C *ᵥ u) ≤ ∑ e, w e * ((C *ᵥ u) e)^2) :
    (C.rank : ℝ) ≤ ∑ e, w e * C e e := by
  let eig := hC.isHermitian.eigenvalues
  let b := hC.isHermitian.eigenvectorBasis
  have heig : ∀ i, 0 ≤ eig i := hC.eigenvalues_nonneg
  have hone : ∀ i, eig i ≠ 0 → 1 ≤ eig i * (∑ e, w e * (b i e)^2) := by
    intro i hi
    let v : I → ℝ := b i
    have hv : v ⬝ᵥ v=1 := by
      have hn := b.orthonormal.1 i
      have hb : inner ℝ (b i) (b i)=1 := by
        rw [real_inner_self_eq_norm_sq, hn]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hb
    have he : C *ᵥ v=eig i • v := hC.isHermitian.mulVec_eigenvectorBasis i
    have hs := hsecond v
    rw [he] at hs
    simp only [dotProduct_smul, smul_eq_mul, hv, mul_one, Pi.smul_apply] at hs
    have heq : (∑ e, w e*(eig i * v e)^2) =
        (eig i)^2 * (∑ e, w e*(v e)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [heq] at hs
    have hp : 0 < eig i := lt_of_le_of_ne (heig i) (Ne.symm hi)
    nlinarith
  rw [hC.isHermitian.rank_eq_card_non_zero_eigs]
  calc
    (Fintype.card {i // eig i ≠ 0} : ℝ) = ∑ i : {i // eig i ≠ 0}, (1:ℝ) := by simp
    _ ≤ ∑ i : {i // eig i ≠ 0}, eig i * (∑ e, w e*(b i e)^2) :=
      Finset.sum_le_sum fun i _ => hone i i.property
    _ = ∑ i, eig i * (∑ e, w e*(b i e)^2) := by
      exact sum_subtype_supported (fun i => eig i ≠ 0)
        (fun i => eig i * (∑ e, w e*(b i e)^2))
        (by intro i hi; rw [not_ne_iff.mp hi, zero_mul])
    _ = ∑ e, w e * C e e := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [spectral_diagonal hC.isHermitian e, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [eig, b]
      ring

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_SeparableCovariance
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators Topology
open Matrix Filter
namespace MatchingEntropy
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separableDefect_attains_max (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope,
      separableLower y-maxMatchingEntropy G y ≤ separableLower x-maxMatchingEntropy G x := by
  have hs : UpperSemicontinuousOn (fun y => separableLower y-maxMatchingEntropy G y)
      G.polytope := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      continuous_separableLower.continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

theorem matching_covariance_rank_face (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ G.faceCodimension x+
      (covariance p (matchingNormalized G x)).rank := by
  let W := weightedDirectionSpace p (matchingNormalized G x)
  let L : G.faceSpace x →ₗ[ℝ] W :=
    ((normalizeLinear x).comp (G.faceSpace x).subtype).codRestrict W
      (fun u => normalized_face_mem G heven hp hopt u.property)
  have hi : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    funext e
    have hh := congrFun (congrArg Subtype.val huv) e
    change u.val e/Real.sqrt (x e.val)=v.val e/Real.sqrt (x e.val) at hh
    exact (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr e.property))).mp hh
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hq := (G.faceSpace x).finrank_quotient_add_finrank
  rw [covariance_rank hp.1.1]
  have hq' : G.faceCodimension x+Module.finrank ℝ (G.faceSpace x)=Fintype.card {e // 0 < x e} := by
    simpa only [LooplessGraph.faceCodimension,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using hq
  change Module.finrank ℝ (G.faceSpace x) ≤ Module.finrank ℝ W at hdim
  dsimp only [W] at hdim
  omega

theorem faceCodimension_strict (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope) :
    G.faceCodimension x < 2*Fintype.card V := by
  by_cases hn4 : 4 ≤ Fintype.card V
  · have hb := LooplessGraph.faceCodimension_strong_aux (Fintype.card V) G rfl heven hn4 x
      (G.polytope_subset_constraintPolytope hx)
    omega
  · have hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1 := by
      rintro ⟨S,_,hlo,hhi,_⟩
      have hh := Finset.card_compl_add_card S
      omega
    have hb := G.faceCodimension_no_tight heven hnt
    omega

omit [Fintype V] [DecidableEq V] in

theorem matching_separable_covariance (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x)
    (u : {e // 0 < x e} → ℝ) :
    u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤
      ∑ e, (1-3*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  let v := G.mean (fun M => p M*a M)
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_separable_second_variation G hp hopt hmax w c hcenter
  have hzero : ∀ e, ¬0 < x e → v e=0 := by
    intro e he
    have he0 : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
    exact mean_score_support G hp.1 a e (by rw [hp.2,he0])
  have hnorm : (∑ e, (v e)^2/x e) =
      ∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
  have hbar : (∑ e, (v e)^2/(1-x e)) =
      ∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
    change (v e.val)^2/(1-x e.val)=x e.val/(1-x e.val)*((v e.val)^2/x e.val)
    field_simp [ne_of_gt e.property]
  have hquad : (∑ M, p M*(a M)^2)=u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change -(∑ e, (v e)^2/x e)+3*(∑ e, (v e)^2/(1-x e))+(∑ M,p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hbar,hquad] at hh
  have heq : (∑ e, (1-3*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) =
      (∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2)-
      3*(∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) := by
    simp_rw [sub_mul,one_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq]
  linarith

omit [Fintype V] [DecidableEq V] in
theorem matching_covariance_diagonal (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) (e : {e // 0<x e}) :
    covariance p (matchingNormalized G x) e e=1-x e.val := by
  rw [covariance_entry hp.1.1]
  have hh := normalizedCentered_variance hp.1.2
    (fun M (e : {e // 0<x e}) => G.indicator M e.val)
    (by intro M e; simp only [LooplessGraph.indicator]; split <;> norm_num)
    (fun e => x e.val) (fun e => congrFun hp.2 e.val) (fun e => e.property) e
  convert hh using 1
  apply Finset.sum_congr rfl
  intro M _
  change p M*matchingNormalized G x M e*matchingNormalized G x M e=
    p M*(matchingNormalized G x M e)^2
  ring

theorem separable_max_has_forced (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x) : ∃ e, x e=1 := by
  by_contra hforced
  push Not at hforced
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  have hsecond := covariance_weighted_rank (covariance_posSemidef p (matchingNormalized G x))
    (fun e => 1-3*x e.val/(1-x e.val)) (matching_separable_covariance G hp hopt hmax)
  have htrace : (∑ e : {e // 0<x e}, (1-3*x e.val/(1-x e.val))*
      covariance p (matchingNormalized G x) e e) = Fintype.card {e // 0<x e}-2*(Fintype.card V:ℝ) := by
    have he (e : {e // 0<x e}) : (1-3*x e.val/(1-x e.val))*
        covariance p (matchingNormalized G x) e e=1-4*x e.val := by
      rw [matching_covariance_diagonal G hp]
      have hh : 1-x e.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (hforced e.val))
      field_simp
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    obtain ⟨r,hr⟩ := heven
    have hv : Fintype.card V=2*r := by omega
    have hs : (∑ e : {e // 0<x e}, x e.val)=(r:ℝ) := by
      rw [← G.marginal_sum hv hx]
      exact (sum_positive_support x x (fun e he =>
        le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
    rw [hs,hv]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [htrace] at hsecond
  have hrank := matching_covariance_rank_face G heven hp hopt
  have hstrict := faceCodimension_strict G heven hn hx
  have hrankR : (Fintype.card {e // 0<x e}:ℝ) ≤ G.faceCodimension x+
      (covariance p (matchingNormalized G x)).rank := by exact_mod_cast hrank
  have hstrictR : (G.faceCodimension x:ℝ)<2*(Fintype.card V:ℝ) := by exact_mod_cast hstrict
  linarith

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_ForcedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators
namespace MatchingEntropy
namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] in
theorem addForced_injective (G : LooplessGraph V E) (e₀ : E) :
    Function.Injective (G.addForced e₀) := by
  intro N N' h
  apply (G.forcedMatchingEquiv e₀).injective
  exact Subtype.ext h

omit [Fintype E] [DecidableEq E] in
theorem remaining_vertex_card (G : LooplessGraph V E) (e₀ : E) :
    Fintype.card {v // G.RemainingVertex e₀ v} + 2 = Fintype.card V := by
  have he : Fintype.card {v // G.Incident v e₀}=2 := by
    rw [Fintype.card_subtype]
    have hf : Finset.univ.filter (fun v => G.Incident v e₀)={G.left e₀, G.right e₀} := by
      ext v
      simp [Incident, eq_comm]
    rw [hf, Finset.card_pair (G.loopless e₀)]
  have h := Fintype.card_subtype_compl (G.Incident · e₀)
  have hle := Fintype.card_subtype_le (G.Incident · e₀)
  change Fintype.card {v // ¬G.Incident v e₀} + 2 = Fintype.card V
  omega

omit [Fintype V] [DecidableEq V] in
theorem law_support_of_mean_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) {e₀ : E} (he : G.mean p e₀=1)
    (M : G.Matching) (hM : e₀ ∉ M.val) : p M=0 := by
  have hz : ∑ N, p N*(1-G.indicator N e₀)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e₀=0
    rw [he, sub_self]
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun N (_ : N ∈ Finset.univ) =>
      mul_nonneg (hp.1 N) (sub_nonneg.mpr (G.indicator_le_one N e₀)))).mp hz M (by simp)
  simpa [indicator,hM] using hh

omit [Fintype V] in

theorem forcedLaw_feasible (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) (e₀ : E) (he : x e₀=1) :
    (fun N => p (G.addForced e₀ N)) ∈ (G.deleteEndpoints e₀).feasibleLaws
      (fun e => x e.val) := by
  have hs : ∀ M, e₀ ∉ M.val → p M=0 :=
    G.law_support_of_mean_one hp.1 (by rw [hp.2,he])
  refine ⟨⟨fun N => hp.1.1 _, ?_⟩, ?_⟩
  · rw [← hp.1.2]
    apply Fintype.sum_of_injective (G.addForced e₀) (G.addForced_injective e₀)
    · intro M hM
      exact hs M (fun hh => hM ((G.range_addForced e₀ M).mpr hh))
    · intro N
      rfl
  · funext e
    rw [← congrFun hp.2 e.val]
    apply Fintype.sum_of_injective (G.addForced e₀) (G.addForced_injective e₀)
    · intro M hM
      rw [hs M (fun hh => hM ((G.range_addForced e₀ M).mpr hh)),zero_mul]
    · intro N
      simp only [indicator,mem_addForced_remaining]

omit [Fintype V] [DecidableEq V] in

theorem forced_coordinate_zero (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) {e : E}
    (hneq : e ≠ e₀) (hrem : ¬G.RemainingEdge e₀ e) : x e=0 := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  rw [← congrFun hp.2 e]
  apply Finset.sum_eq_zero
  intro M _
  by_cases hM : e₀ ∈ M.val
  · have hh : e ∉ M.val := fun hh => hrem (G.matching_remaining e₀ M hM hh hneq)
    simp [indicator,hh]
  · rw [G.law_support_of_mean_one hp.1 (by rw [hp.2,he]) M hM,zero_mul]

omit [Fintype V] in

theorem separableLower_forced (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    separableLower (fun e : {e // G.RemainingEdge e₀ e} => x e.val)=separableLower x := by
  have hz : ∀ e, ¬G.RemainingEdge e₀ e →
      Real.negMulLog (x e)=0 ∧ Real.negMulLog (1-x e)=0 := by
    intro e h
    by_cases hneq : e=e₀
    · simp [hneq,he]
    · simp [G.forced_coordinate_zero hx e₀ he hneq h]
  unfold separableLower entropy
  rw [sum_subtype_supported _ _ (fun e h => (hz e h).1),
    sum_subtype_supported _ _ (fun e h => (hz e h).2)]

end LooplessGraph

theorem entropy_fiberMass_injective {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f) :
    entropy (fiberMass p f)=entropy p := by
  classical
  have hself (a : A) : fiberMass p f (f a)=p a := by
    simp [fiberMass,hf.eq_iff]
  have hzero (b : B) (hb : b ∉ Set.range f) : fiberMass p f b=0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact ite_eq_right (fun h => hb ⟨a,h⟩)
  symm
  apply Fintype.sum_of_injective f hf
  · intro b hb
    rw [hzero b hb,Real.negMulLog_zero]
  · intro a
    rw [hself]

namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
omit [Fintype V] in

theorem liftForced_feasible (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1)
    {q : (G.deleteEndpoints e₀).Matching → ℝ}
    (hq : q ∈ (G.deleteEndpoints e₀).feasibleLaws (fun e => x e.val)) :
    fiberMass q (G.addForced e₀) ∈ G.feasibleLaws x := by
  refine ⟨fiberMass_mem_simplex hq.1 _, ?_⟩
  funext e
  rw [mean,fiberMass_expect]
  by_cases heq : e=e₀
  · subst e
    simpa [indicator] using hq.1.2.trans he.symm
  · by_cases hr : G.RemainingEdge e₀ e
    · change (∑ N, q N*G.indicator (G.addForced e₀ N) e)=_
      have hm (N : (G.deleteEndpoints e₀).Matching) :
          G.indicator (G.addForced e₀ N) e = (G.deleteEndpoints e₀).indicator N ⟨e,hr⟩ := by
        simp only [indicator,G.mem_addForced_remaining e₀ N ⟨e,hr⟩]
      simp_rw [hm]
      exact congrFun hq.2 ⟨e,hr⟩
    · rw [G.forced_coordinate_zero hx e₀ he heq hr]
      apply Finset.sum_eq_zero
      intro N _
      simp [indicator,heq,hr]

omit [Fintype V] in

theorem maxMatchingEntropy_forced_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    maxMatchingEntropy (G.deleteEndpoints e₀) (fun e => x e.val) ≤ maxMatchingEntropy G x := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  have hr := G.forcedLaw_feasible hp e₀ he
  have hx' := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hr⟩
  obtain ⟨q,hq,hopt⟩ := maxMatchingEntropy_attained (G.deleteEndpoints e₀) hx'
  rw [← hopt,← entropy_fiberMass_injective q _ (G.addForced_injective e₀)]
  exact entropy_le_maxMatchingEntropy G (G.liftForced_feasible hx e₀ he hq)

end LooplessGraph
end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_SeparableLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators Topology
namespace MatchingEntropy

theorem separable_lower_aux (n : ℕ) :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), Fintype.card V=n → Even n →
      ∀ x ∈ G.polytope, separableLower x ≤ maxMatchingEntropy G x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ G hcard heven y hy
    by_cases hn : n=0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
      simpa [separableLower,entropy] using maxMatchingEntropy_nonneg G hy
    · have heven' : Even (Fintype.card V) := hcard ▸ heven
      have hPM : Nonempty G.Matching := by
        obtain ⟨p,hp⟩ := (G.mem_polytope_iff y).mp hy
        by_contra h
        have : IsEmpty G.Matching := not_nonempty_iff.mp h
        simpa using hp.1.2
      obtain ⟨x,hx,hmax⟩ := separableDefect_attains_max G heven' hPM
      obtain ⟨e₀,he₀⟩ := separable_max_has_forced G heven' (by omega) hx hmax
      have hc := G.remaining_vertex_card e₀
      have hlt : Fintype.card {v // G.RemainingVertex e₀ v}<n := by omega
      have hev : Even (Fintype.card {v // G.RemainingVertex e₀ v}) := by
        obtain ⟨r,hr⟩ := heven
        refine ⟨r-1,?_⟩
        omega
      obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
      have hs := G.forcedLaw_feasible hp e₀ he₀
      have hxr := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hs⟩
      have hsmall := ih _ hlt (G.deleteEndpoints e₀) rfl hev _ hxr
      rw [G.separableLower_forced hx e₀ he₀] at hsmall
      have hxbound := hsmall.trans (G.maxMatchingEntropy_forced_le hx e₀ he₀)
      have hcompare := hmax y hy
      linarith

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separable_lower (G : LooplessGraph V E) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) : separableLower x ≤ maxMatchingEntropy G x := by
  obtain ⟨M⟩ := hPM
  have hev : Even (Fintype.card V) := ⟨M.val.card, by have hh := G.matching_card_twice M; omega⟩
  exact separable_lower_aux (Fintype.card V) G rfl hev x hx

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_EntropyUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators
namespace MatchingEntropy

theorem entropy_le_subprob_crossEntropy {I : Type*} [Fintype I] {p q : I → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i ≤ 1) (hq : q ∈ probabilitySimplex I)
    (hsupp : ∀ i, p i=0 → q i=0) :
    entropy q ≤ -∑ i, q i*Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤ -(q i*Real.log (p i))+p i-q i := by
    intro i
    by_cases hi : p i=0
    · simp [hi,hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib,hq.2] at hh
  change entropy q ≤ -(∑ i, q i*Real.log (p i))+(∑ i,p i)-1 at hh
  linarith

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem matchingBits_injective (G : LooplessGraph V E) : Function.Injective G.matchingBits := by
  intro M N h
  apply Subtype.ext
  ext e
  have he := congrFun h e
  simpa only [matchingBits,decide_eq_decide] using he

end LooplessGraph

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem productBoolean_nonneg {x : E → ℝ} (hx : ∀ e, x e ∈ Set.Icc (0:ℝ) 1)
    (b : E → Bool) : 0 ≤ productBoolean x b := by
  apply Finset.prod_nonneg
  intro e _
  split
  · exact (hx e).1
  · exact sub_nonneg.mpr (hx e).2

omit [Fintype V] [DecidableEq V] in
theorem productBoolean_sum (x : E → ℝ) : (∑ b : E → Bool, productBoolean x b)=1 := by
  unfold productBoolean
  rw [← Fintype.prod_sum (fun e (b : Bool) => if b then x e else 1-x e)]
  simp

omit [Fintype V] [DecidableEq V] in
theorem matchingBoolean_sum_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : ∀ e, x e ∈ Set.Icc (0:ℝ) 1) :
    (∑ M, productBoolean x (G.matchingBits M)) ≤ 1 := by
  rw [← productBoolean_sum x]
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image G.matchingBits, productBoolean x b := by
      rw [Finset.sum_image]
      intro M _ N _ h
      exact G.matchingBits_injective h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => productBoolean_nonneg hx b)

omit [Fintype V] [DecidableEq V] in
theorem matching_boolean_factor_pos (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {M : G.Matching} (hM : 0<p M) (e : E) :
    0<(if G.matchingBits M e then x e else 1-x e) := by
  unfold LooplessGraph.matchingBits
  by_cases he : e ∈ M.val
  · simp only [he,decide_true,ite_true]
    have hh := Finset.single_le_sum (f := fun N => p N*G.indicator N e)
      (s := Finset.univ) (fun N _ => mul_nonneg (hp.1.1 N) (G.indicator_nonneg N e))
      (Finset.mem_univ M)
    have hm : G.indicator M e=1 := by simp [LooplessGraph.indicator,he]
    rw [hm,mul_one] at hh
    change p M ≤ G.mean p e at hh
    rw [hp.2] at hh
    exact hM.trans_le hh
  · simp only [he,decide_false]
    have hh := Finset.single_le_sum (f := fun N => p N*(1-G.indicator N e))
      (s := Finset.univ) (fun N _ => mul_nonneg (hp.1.1 N)
        (sub_nonneg.mpr (G.indicator_le_one N e))) (Finset.mem_univ M)
    have hm : G.indicator M e=0 := by simp [LooplessGraph.indicator,he]
    simp only [hm,sub_zero,mul_one,mul_sub,Finset.sum_sub_distrib,hp.1.2] at hh
    change p M ≤ 1-G.mean p e at hh
    rw [hp.2] at hh
    exact hM.trans_le hh

omit [Fintype V] [DecidableEq V] in

theorem matching_entropy_le_binary (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) : entropy p ≤ binaryEntropy x := by
  have hx := G.coordinate_mem_Icc ((G.mem_polytope_iff x).mpr ⟨p,hp⟩)
  have hprod (M : G.Matching) (hM : 0<p M) : 0<productBoolean x (G.matchingBits M) :=
    Finset.prod_pos (fun e _ => matching_boolean_factor_pos G hp hM e)
  have hcross := entropy_le_subprob_crossEntropy
    (fun M => productBoolean_nonneg hx (G.matchingBits M)) (matchingBoolean_sum_le G hx) hp.1
    (fun M hzero => le_antisymm (le_of_not_gt (fun hM => (ne_of_gt (hprod M hM)) hzero)) (hp.1.1 M))
  have hlog (M : G.Matching) : p M*Real.log (productBoolean x (G.matchingBits M)) =
      ∑ e, p M*(G.indicator M e*Real.log (x e)+(1-G.indicator M e)*Real.log (1-x e)) := by
    by_cases hzero : p M=0
    · simp [hzero]
    · have hpos : 0<p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hzero)
      rw [productBoolean,Real.log_prod (fun e _ => ne_of_gt (matching_boolean_factor_pos G hp hpos e)),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      simp only [LooplessGraph.matchingBits,LooplessGraph.indicator]
      by_cases he : e ∈ M.val <;> simp [he]
  have heq : -(∑ M, p M*Real.log (productBoolean x (G.matchingBits M)))=binaryEntropy x := by
    simp_rw [hlog]
    rw [Finset.sum_comm]
    have he (e : E) : (∑ M, p M*(G.indicator M e*Real.log (x e)+
        (1-G.indicator M e)*Real.log (1-x e)))=
        x e*Real.log (x e)+(1-x e)*Real.log (1-x e) := by
      simp_rw [mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul]
      have hmean : (∑ M,p M*G.indicator M e)=x e := congrFun hp.2 e
      have hbar : (∑ M,p M*(1-G.indicator M e))=1-x e := by
        simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib,hp.1.2,hmean]
      rw [hmean,hbar]
    simp_rw [he]
    rw [Finset.sum_add_distrib,neg_add_rev]
    dsimp only [binaryEntropy]
    rw [entropy_eq,entropy_eq]
    ring
  rwa [heq] at hcross

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_le_binary (G : LooplessGraph V E) (x : E → ℝ)
    (hx : x ∈ G.polytope) : maxMatchingEntropy G x ≤ binaryEntropy x := by
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  rw [← hopt]
  exact matching_entropy_le_binary G hp

end MatchingEntropy
end
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

lemma expLaw_simplex [Nonempty I] (a : I → ℝ) : expLaw a∈probabilitySimplex I := by
  refine ⟨fun i => (div_pos (Real.exp_pos _) (expSum_pos a)).le,?_⟩
  simp only [expLaw,←sum_div]
  exact div_self (expSum_pos a).ne'

lemma log_expLaw [Nonempty I] (a : I → ℝ) (i : I) :
    Real.log (expLaw a i)=a i-Real.log (expSum a) := by
  rw [expLaw,Real.log_div (Real.exp_ne_zero _) (expSum_pos a).ne',Real.log_exp]

lemma expLaw_cross [Nonempty I] (a : I → ℝ) {p : I → ℝ}
    (hp : p∈probabilitySimplex I) :
    -(∑ i,p i*Real.log (expLaw a i))=Real.log (expSum a)-∑ i,p i*a i := by
  simp only [log_expLaw,mul_sub,sum_sub_distrib,←sum_mul,hp.2,one_mul]
  ring

lemma expSum_variational_le [Nonempty I] (a : I → ℝ) {p : I → ℝ}
    (hp : p∈probabilitySimplex I) : entropy p+∑ i,p i*a i≤Real.log (expSum a) := by
  have hh := entropy_le_crossEntropy (expLaw_simplex a) hp
    (fun i hi => False.elim ((div_pos (Real.exp_pos _) (expSum_pos a)).ne' hi))
  rw [expLaw_cross a hp] at hh
  linarith

lemma expSum_variational_eq [Nonempty I] (a : I → ℝ) :
    entropy (expLaw a)+∑ i,expLaw a i*a i=Real.log (expSum a) := by
  rw [entropy_eq,expLaw_cross a (expLaw_simplex a)]
  ring

namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
lemma score_indicator (G : LooplessGraph V E) (β : E → ℝ) (M : G.Matching) :
    G.score β M=∑ e, β e*G.indicator M e := by
  simp [score,indicator]

omit [Fintype V] [DecidableEq V] in
lemma mean_score (G : LooplessGraph V E) (β : E → ℝ) (p : G.Matching → ℝ) :
    (∑ M,p M*G.score β M)=∑ e,β e*G.mean p e := by
  simp only [score_indicator,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro e _
  simp only [mean,mul_sum]
  apply sum_congr rfl; intro M _; ring

omit [Fintype V] [DecidableEq V] in
lemma complement_entropy_le_mass (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x∈G.polytope) : entropy (fun e => 1-x e)≤∑ e,x e := by
  apply sum_le_sum; intro e _
  have hh := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr (G.coordinate_mem_Icc hx e).2)
  simpa only [sub_sub_cancel] using hh

lemma entropy_binary_scale (G : LooplessGraph V E) (hPM : Nonempty G.Matching)
    {r : ℕ} (hV : Fintype.card V=2*r) {x : E → ℝ} (hx : x∈G.polytope) :
    entropy x/Real.log 2-4*(Fintype.card V:ℝ)≤ maxMatchingEntropy G x/Real.log 2 ∧
    maxMatchingEntropy G x/Real.log 2≤entropy x/Real.log 2+(Fintype.card V:ℝ) := by
  have hl := separable_lower G hPM x hx
  have hu := maxMatchingEntropy_le_binary G x hx
  have hc := G.complement_entropy_le_mass hx
  rw [G.marginal_sum hV hx] at hc
  have hv : (Fintype.card V:ℝ)=2*(r:ℝ) := by exact_mod_cast hV
  have hlog := BinaryMatching.Algorithm.half_le_log_two
  have hr : (0:ℝ)≤r := by positivity
  have hprod := mul_le_mul_of_nonneg_right hlog hr
  dsimp only [separableLower,binaryEntropy] at hl hu
  constructor
  · apply (le_div_iff₀ BinaryMatching.Algorithm.log_two_pos).2
    rw [sub_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne',hv]
    nlinarith
  · apply (div_le_iff₀ BinaryMatching.Algorithm.log_two_pos).2
    rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne',hv]
    nlinarith

omit [Fintype V] [DecidableEq V] in
lemma weighted_variational_le (G : LooplessGraph V E) [Nonempty G.Matching]
    (β : E → ℝ) {x : E → ℝ} (hx : x∈G.polytope) :
    maxMatchingEntropy G x/Real.log 2+∑ e,β e*x e≤Real.log (G.weightedZ β)/Real.log 2 := by
  obtain ⟨p,hp,hh⟩ := maxMatchingEntropy_attained G hx
  have h := expSum_variational_le (fun M => Real.log 2*G.score β M) hp.1
  have he : (∑ M,p M*(Real.log 2*G.score β M))=Real.log 2*(∑ e,β e*x e) := by
    rw [mul_sum]
    conv_lhs => arg 2; ext M; rw [mul_left_comm]
    rw [←mul_sum,G.mean_score,hp.2,mul_sum]
  rw [he,hh] at h
  apply (le_div_iff₀ BinaryMatching.Algorithm.log_two_pos).2
  calc
    _ = maxMatchingEntropy G x+Real.log 2*(∑ e,β e*x e) := by
      rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne']; ring
    _ ≤ _ := h

omit [Fintype V] [DecidableEq V] in
lemma weighted_variational_attained (G : LooplessGraph V E) [Nonempty G.Matching]
    (β : E → ℝ) : ∃ x∈G.polytope,
      Real.log (G.weightedZ β)/Real.log 2≤ maxMatchingEntropy G x/Real.log 2+∑ e,β e*x e := by
  let p := expLaw (fun M => Real.log 2*G.score β M)
  have hp := expLaw_simplex (fun M => Real.log 2*G.score β M)
  have hpx : p∈G.feasibleLaws (G.mean p) := ⟨hp,rfl⟩
  refine ⟨G.mean p,(G.mem_polytope_iff _).mpr ⟨p,hpx⟩,?_⟩
  have he := expSum_variational_eq (fun M => Real.log 2*G.score β M)
  have he' : (∑ M,p M*(Real.log 2*G.score β M))=Real.log 2*(∑ e,β e*G.mean p e) := by
    calc
      _ = Real.log 2*(∑ M,p M*G.score β M) := by
        rw [mul_sum]; apply sum_congr rfl; intro M _; ring
      _ = _ := by rw [G.mean_score]
  change entropy p+(∑ M,p M*(Real.log 2*G.score β M))=Real.log (G.weightedZ β) at he
  rw [he'] at he
  apply (div_le_iff₀ BinaryMatching.Algorithm.log_two_pos).2
  have hH := entropy_le_maxMatchingEntropy G hpx
  calc
    _ ≤ maxMatchingEntropy G (G.mean p)+Real.log 2*(∑ e,β e*G.mean p e) := by linarith
    _ = _ := by rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne']; ring
end LooplessGraph
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

lemma mass_half {n : ℕ} (heven : Even n) {x : Pair n → ℝ}
    (hx : x∈(completeGraph n).polytope) : (∑ e,x e)=(n:ℝ)/2 := by
  obtain ⟨r,hr⟩ := heven
  have hn : Fintype.card (Fin n)=2*r := by simp; omega
  rw [(completeGraph n).marginal_sum hn hx]
  have hn' : (n:ℝ)=2*(r:ℝ) := by exact_mod_cast (show n=2*r by omega)
  rw [hn']; ring

lemma q_dyadic_le_one (n : ℕ) : (q n:ℝ)*dyadic (K n)≤1 := by
  have hh : (q n:ℝ)≤(2:ℝ)^(K n) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) (q n)
  rw [dyadic,inv_pow,←div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr hh

lemma objective_compare (G : Input) (hn : 2≤ G.n) (heven : Even G.n)
    {x : Pair G.n → ℝ} (hx : x∈(completeGraph G.n).polytope) :
    objective G x≤ smoothObjective G x ∧ smoothObjective G x≤ objective G x+G.n := by
  have he : smoothObjective G x-objective G x=
      ∑ e,(phi (x e)-psiReal (K G.n) (x e)) := by
    simp only [smoothObjective,objective,phi,entropy,sum_add_distrib,sum_sub_distrib,←sum_div]
    ring
  have hnon : 0≤∑ e,(phi (x e)-psiReal (K G.n) (x e)) :=
    sum_nonneg fun e _ => (dyadic_entropy_error (K G.n) ((completeGraph G.n).coordinate_mem_Icc hx e)).1
  have hupper : (∑ e,(phi (x e)-psiReal (K G.n) (x e)))≤(G.n:ℝ)/2+1 := by
    calc
      _ ≤ ∑ e,(x e+dyadic (K G.n)) := sum_le_sum fun e _ =>
        (dyadic_entropy_error (K G.n) ((completeGraph G.n).coordinate_mem_Icc hx e)).2
      _ = (G.n:ℝ)/2+(q G.n:ℝ)*dyadic (K G.n) := by
        rw [sum_add_distrib,mass_half heven hx]; simp [q]
      _ ≤ _ := by linarith [q_dyadic_le_one G.n]
  have hn' : (2:ℝ)≤ G.n := by exact_mod_cast hn
  constructor <;> linarith

lemma smooth_lower_partition (G : Input) (hn : 4≤ G.n) (heven : Even G.n)
    {x : Pair G.n → ℝ} (hx : x∈(completeGraph G.n).polytope) :
    smoothObjective G x-4*(G.n:ℝ)≤ logZ G := by
  have hPM := complete_matching_nonempty hn heven
  obtain ⟨r,hr⟩ := heven
  have hn' : Fintype.card (Fin G.n)=2*r := by simp; omega
  have hent := ((completeGraph G.n).entropy_binary_scale hPM hn' hx).1
  have hvar := (completeGraph G.n).weighted_variational_le (fun e => (beta G e:ℝ)) hx
  simp only [Fintype.card_fin] at hent
  dsimp only [smoothObjective,logZ,Z]
  linarith

lemma smooth_upper_partition (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    ∃ x∈(completeGraph G.n).polytope,logZ G≤ smoothObjective G x+G.n := by
  have hPM := complete_matching_nonempty hn heven
  obtain ⟨x,hx,hvar⟩ := (completeGraph G.n).weighted_variational_attained (fun e => (beta G e:ℝ))
  obtain ⟨r,hr⟩ := heven
  have hn' : Fintype.card (Fin G.n)=2*r := by simp; omega
  have hent := ((completeGraph G.n).entropy_binary_scale hPM hn' hx).2
  simp only [Fintype.card_fin] at hent
  refine ⟨x,hx,?_⟩
  dsimp only [smoothObjective,logZ,Z]
  linarith

theorem R_partition_bracket_oai (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    (R G:ℝ)-4*(G.n:ℝ)≤ logZ G ∧ logZ G≤(R G:ℝ)+3*(G.n:ℝ) := by
  obtain ⟨⟨y,hy,hylow⟩,hupp⟩ := R_objective_bracket G hn heven
  constructor
  · have hobj := (objective_compare G (by omega) heven hy).1
    have hpart := smooth_lower_partition G hn heven hy
    linarith
  · obtain ⟨x,hx,hpart⟩ := smooth_upper_partition G hn heven
    have hobj := (objective_compare G (by omega) heven hx).2
    have hU := hupp x hx
    have hn' : (4:ℝ)≤ G.n := by exact_mod_cast hn
    linarith

end
end BinaryMatching.Algorithm
end

end OAI
end

theorem solution : type_of% @OAI.BinaryMatching.Algorithm.R_partition_bracket_oai := @OAI.BinaryMatching.Algorithm.R_partition_bracket_oai
