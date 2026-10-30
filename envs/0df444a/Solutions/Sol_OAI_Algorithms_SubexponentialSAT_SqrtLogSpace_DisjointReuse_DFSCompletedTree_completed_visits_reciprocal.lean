-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:55:55.013995+00:00
-- url     : https://prove2.me/submissions/e099e696-e54a-4ebb-9060-37da95c05d31

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S064

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BranchTree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Counting binary branch-tree paths

False labels an A edge and true labels a B edge. A word is encoded injectively
by its length and the finite set of positions occupied by B. This proves the
finite counting step in Appendix A.3 without any analytic hypotheses.
-/

namespace SubexponentialSAT.BranchTree

open Finset
open scoped BigOperators

/-- The B-position set is contained in the range of the path length. -/
theorem bPositions_subset (p : List Bool) : bPositions p ⊆ range p.length :=
  filter_subset _ _

/-- Depth and B positions determine every edge of a binary path. -/
theorem eq_of_length_bPositions_eq {p q : List Bool}
    (hlen : p.length = q.length) (hpos : bPositions p = bPositions q) : p = q := by
  apply List.ext_getElem hlen
  intro i hp hq
  have he : (p[i]'hp = true) ↔ (q[i]'hq = true) := by
    have hm : i ∈ bPositions p ↔ i ∈ bPositions q := by rw [hpos]
    simpa [mem_bPositions, hp, hq, List.getElem?_eq_getElem] using hm
  cases hvp : p[i]'hp <;> cases hvq : q[i]'hq <;> simp_all

theorem pathCode_injective : Function.Injective pathCode := by
  intro p q h
  exact eq_of_length_bPositions_eq (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem mem_positionSets {D R : ℕ} {s : Finset ℕ} :
    s ∈ positionSets D R ↔ s ⊆ range D ∧ s.card ≤ R := by
  simp only [positionSets, mem_biUnion, mem_range, mem_powersetCard]
  constructor
  · rintro ⟨r, hr, hs, he⟩
    exact ⟨hs, he ▸ Nat.le_of_lt_succ hr⟩
  · rintro ⟨hs, hc⟩
    exact ⟨s.card, Nat.lt_succ_of_le hc, hs, rfl⟩

theorem card_positionSets_le (D R : ℕ) :
    (positionSets D R).card ≤ ∑ r ∈ range (R + 1), D.choose r := by
  calc
    (positionSets D R).card ≤
        ∑ r ∈ range (R + 1), ((range D).powersetCard r).card := card_biUnion_le
    _ = ∑ r ∈ range (R + 1), D.choose r := by simp

/-- Every finite collection of actual binary paths obeys the node-count bound.
Prefix closure is unnecessary for this stronger statement. -/
theorem card_paths_le (P : Finset (List Bool)) (D R : ℕ)
    (hdepth : ∀ p ∈ P, p.length ≤ D)
    (hB : ∀ p ∈ P, (bPositions p).card ≤ R) :
    P.card ≤ (D + 1) * ∑ r ∈ range (R + 1), D.choose r := by
  have hsub : P.image pathCode ⊆ range (D + 1) ×ˢ positionSets D R := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hc
    apply mem_product.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le (hdepth p hp)), ?_⟩
    apply mem_positionSets.mpr
    refine ⟨?_, hB p hp⟩
    exact (bPositions_subset p).trans (range_mono (hdepth p hp))
  calc
    P.card = (P.image pathCode).card := (card_image_of_injective P pathCode_injective).symm
    _ ≤ (range (D + 1) ×ˢ positionSets D R).card := card_le_card hsub
    _ = (D + 1) * (positionSets D R).card := by simp
    _ ≤ (D + 1) * ∑ r ∈ range (R + 1), D.choose r :=
      Nat.mul_le_mul_left _ (card_positionSets_le D R)

/-- Appendix A.3's finite-tree bound, with every internal node included. -/
theorem Tree.nodeCount_le (t : Tree) (D R : ℕ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ D)
    (hB : ∀ p ∈ t.paths, (bPositions p).card ≤ R) :
    t.nodeCount ≤ (D + 1) * ∑ r ∈ range (R + 1), D.choose r := by
  rw [← t.card_paths]
  exact card_paths_le t.paths D R hdepth hB

end SubexponentialSAT.BranchTree

namespace SubexponentialSAT.BranchTree

/-- A uniform binomial estimate valid at a real, not necessarily integral, cutoff. -/
theorem choose_le_rpow_real (D r : ℕ) {q : ℝ} (hq : 0 < q)
    (hD : q ≤ D) (hr : (r : ℝ) ≤ q) :
    (D.choose r : ℝ) ≤ (4 * (D : ℝ) / q) ^ q := by
  have hbase : 1 ≤ (D : ℝ) / q := (le_div_iff₀ hq).2 (by simpa using hD)
  have hbasenonneg : 0 ≤ (D : ℝ) / q := le_trans zero_le_one hbase
  have hsplit : (D : ℝ) ^ r / (r.factorial : ℝ) =
      ((D : ℝ) / q) ^ r * (q ^ r / (r.factorial : ℝ)) := by
    rw [div_pow]
    field_simp
  have hpow : ((D : ℝ) / q) ^ r ≤ ((D : ℝ) / q) ^ q := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hbase hr)
  have hexp : Real.exp q ≤ (4 : ℝ) ^ q := by
    rw [← Real.exp_one_rpow]
    exact Real.rpow_le_rpow (Real.exp_nonneg _) (by linarith [Real.exp_one_lt_d9]) hq.le
  calc
    (D.choose r : ℝ) ≤ (D : ℝ) ^ r / (r.factorial : ℝ) := Nat.choose_le_pow_div r D
    _ = ((D : ℝ) / q) ^ r * (q ^ r / (r.factorial : ℝ)) := hsplit
    _ ≤ ((D : ℝ) / q) ^ r * Real.exp q :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp q hq.le r)
        (pow_nonneg hbasenonneg r)
    _ ≤ ((D : ℝ) / q) ^ q * Real.exp q :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg q)
    _ ≤ ((D : ℝ) / q) ^ q * (4 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hbasenonneg _)
    _ = (4 * (D : ℝ) / q) ^ q := by
      rw [← Real.mul_rpow hbasenonneg (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

end SubexponentialSAT.BranchTree

namespace SubexponentialSAT.BranchTree
open Finset
open scoped BigOperators

/-- The finite path bound with an arbitrary positive real cutoff. -/
theorem card_paths_le_rpow_real (P : Finset (List Bool)) (D R : ℕ) {q : ℝ}
    (hq : 0 < q) (hD : q ≤ D) (hR : (R : ℝ) ≤ q)
    (hdepth : ∀ p ∈ P, p.length ≤ D)
    (hB : ∀ p ∈ P, (bPositions p).card ≤ R) :
    (P.card : ℝ) ≤ ((D : ℝ) + 1) * ((R : ℝ) + 1) * (4 * (D : ℝ) / q) ^ q := by
  have hcount : (P.card : ℝ) ≤ ((D : ℝ) + 1) *
      ∑ r ∈ range (R + 1), (D.choose r : ℝ) := by
    exact_mod_cast card_paths_le P D R hdepth hB
  calc
    (P.card : ℝ) ≤ ((D : ℝ) + 1) *
        ∑ r ∈ range (R + 1), (D.choose r : ℝ) := hcount
    _ ≤ ((D : ℝ) + 1) * ∑ _r ∈ range (R + 1), (4 * (D : ℝ) / q) ^ q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro r hr
      apply choose_le_rpow_real D r hq hD
      exact (Nat.cast_le.mpr (Nat.le_of_lt_succ (mem_range.mp hr))).trans hR
    _ = ((D : ℝ) + 1) * ((R : ℝ) + 1) * (4 * (D : ℝ) / q) ^ q := by
      simp [mul_assoc]

/-- The only budget used here is the explicit logarithmic exponent inequality. -/
theorem card_paths_le_two_rpow (P : Finset (List Bool)) (D R : ℕ) {q e : ℝ}
    (hq : 0 < q) (hD : q ≤ D) (hR : (R : ℝ) ≤ q)
    (hdepth : ∀ p ∈ P, p.length ≤ D)
    (hB : ∀ p ∈ P, (bPositions p).card ≤ R)
    (hbudget : q * Real.log (4 * (D : ℝ) / q) ≤ Real.log 2 * e) :
    (P.card : ℝ) ≤ ((D : ℝ) + 1) * ((R : ℝ) + 1) * (2 : ℝ) ^ e := by
  have hDpos : 0 < (D : ℝ) := hq.trans_le hD
  have hbpos : 0 < 4 * (D : ℝ) / q := by positivity
  have hexp : (4 * (D : ℝ) / q) ^ q ≤ (2 : ℝ) ^ e := by
    rw [Real.rpow_def_of_pos hbpos, Real.rpow_def_of_pos (by norm_num), Real.exp_le_exp]
    simpa only [mul_comm] using hbudget
  exact (card_paths_le_rpow_real P D R hq hD hR hdepth hB).trans
    (mul_le_mul_of_nonneg_left hexp (by positivity))

end SubexponentialSAT.BranchTree

namespace SubexponentialSAT.BranchTree
open Finset

theorem bPositions_cons (b : Bool) (p : List Bool) :
    bPositions (b :: p) = (if b then {0} else ∅) ∪ (bPositions p).image Nat.succ := by
  ext i
  cases i with
  | zero => cases b <;> simp [mem_bPositions]
  | succ i => cases b <;> simp [mem_bPositions, mem_image]

theorem card_bPositions_cons (b : Bool) (p : List Bool) :
    (bPositions (b :: p)).card = (if b then 1 else 0) + (bPositions p).card := by
  rw [bPositions_cons]
  cases b <;> simp [card_image_of_injective _ Nat.succ_injective, Nat.add_comm]

theorem card_bPositions_eq_count (p : List Bool) :
    (bPositions p).card = p.count true := by
  induction p with
  | nil => simp [bPositions]
  | cons b p ih =>
    rw [card_bPositions_cons, ih]
    cases b <;> simp [Nat.add_comm]

end SubexponentialSAT.BranchTree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SunflowerBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal-set sunflower branching

Concrete CNF children and their semantic union, together with the absorption
invariants used by the cumulative-insertion argument. Opposite polarities are
distinct literals; no variable-disjointness premise is used.
-/

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

theorem sdiff_injective_on {F : CNF V} {H : Clause V}
    (hcore : ∀ C ∈ F, H ⊆ C) : Set.InjOn (fun C => C \ H) F := by
  intro C hC D hD heq
  change C \ H = D \ H at heq
  calc
    C = H ∪ (C \ H) := (Finset.union_sdiff_of_subset (hcore C hC)).symm
    _ = H ∪ (D \ H) := congrArg (fun P => H ∪ P) heq
    _ = D := Finset.union_sdiff_of_subset (hcore D hD)

end SubexponentialSAT.SunflowerBranch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem formulaSet_filter (F : Formula α) (p : Clause α → Bool)
    (q : Finset α → Prop) [DecidablePred q]
    (hp : ∀ C, p C = true ↔ q (clauseSet C)) :
    formulaSet (F.filter p) = (formulaSet F).filter q := by
  ext C
  simp only [mem_formulaSet, Finset.mem_filter]
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hD, htest⟩ := List.mem_filter.mp hD
    exact ⟨⟨D, hD, rfl⟩, (hp D).mp htest⟩
  · rintro ⟨⟨D, hD, rfl⟩, hq⟩
    exact ⟨D, List.mem_filter.mpr ⟨hD, (hp D).mpr hq⟩, rfl⟩

@[simp] theorem formulaSet_removeTautologies (neg : α → α) (F : Formula α) :
    formulaSet (removeTautologies neg F) =
      (formulaSet F).filter (fun C => ¬ ∃ x ∈ C, neg x ∈ C) := by
  apply formulaSet_filter
  intro C
  simp only [not_true_iff, tautology_true]

@[simp] theorem formulaSet_absorb (F : Formula α) :
    formulaSet (absorb F) =
      (formulaSet F).filter (fun C => ¬ ∃ D ∈ formulaSet F, D ⊂ C) := by
  change formulaSet ((dedupClauses F).filter _) = _
  rw [formulaSet_filter (dedupClauses F) _
    (fun C => ¬ ∃ D ∈ formulaSet F, D ⊂ C)]
  · rw [formulaSet_dedupClauses]
  · intro C
    simp only [not_true_iff, any_strictSubset_true]

@[simp] theorem formulaSet_eraseClauses (F S : Formula α) :
    formulaSet (eraseClauses F S) = formulaSet F \ formulaSet S := by
  unfold eraseClauses
  rw [formulaSet_filter F _ (fun C => C ∉ formulaSet S)]
  · ext C
    simp
  · intro C
    simp only [not_true_iff, any_equivalent_true]

section SAT
variable {V : Type u} [DecidableEq V]

@[simp] theorem absorb_set (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (absorb F) = SubexponentialSAT.SAT.absorb (formulaSet F) := formulaSet_absorb F

@[simp] theorem normalize_set (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (normalize SubexponentialSAT.SAT.Literal.negate F) = SubexponentialSAT.SAT.normalize (formulaSet F) := by
  simp only [normalize, absorb_set, formulaSet_removeTautologies, formulaSet_cleanLiterals]
  rfl

end SAT
end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RemovalCharging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Appendix A.2: charging removals to smaller insertions

The trace below records finite clause families before and after each replacement.
The cumulative insertion counter counts events, not distinct clauses.  Its
accounting identity therefore does not assume that reinsertion is impossible.
-/

namespace SubexponentialSAT.RemovalCharging

open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
/-- A finite relation covering its source gives an upper bound by the sum of
the sizes of its target fibers. No disjointness of fibers is required. -/
theorem card_le_mul_of_cover (s : Finset α) (t : Finset β)
    (r : α → β → Prop) [DecidableRel r] (M : ℕ)
    (hcover : ∀ a ∈ s, ∃ b ∈ t, r a b)
    (hcap : ∀ b ∈ t, (s.filter fun a => r a b).card ≤ M) :
    s.card ≤ M * t.card := by
  have hsub : s ⊆ t.biUnion (fun b => s.filter fun a => r a b) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcover a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
  calc
    s.card ≤ (t.biUnion (fun b => s.filter fun a => r a b)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ t, (s.filter fun a => r a b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ t, M := Finset.sum_le_sum hcap
    _ = M * t.card := by simp [Nat.mul_comm]

/-- Summing per-literal bounds controls the number of live nonempty clauses. -/
theorem widthCount_le_universe_mul (F : Family α) (U : Finset α) (j M : ℕ)
    (hnonempty : ∀ C ∈ F, C.Nonempty)
    (hsupport : ∀ C ∈ F, C ⊆ U)
    (hdegree : ∀ a, widthLiteralDegree F j a ≤ M) :
    widthCount F j ≤ M * U.card := by
  apply card_le_mul_of_cover (F.filter fun C => C.card = j) U
    (fun C a => a ∈ C) M
  · intro C hC
    have hCF := (Finset.mem_filter.mp hC).1
    obtain ⟨a, ha⟩ := hnonempty C hCF
    exact ⟨a, hsupport C hCF ha, ha⟩
  · intro a _
    simpa [widthLiteralDegree, Finset.filter_filter] using hdegree a

namespace Trace

variable {T : ℕ} (tr : Trace α T)

theorem live_subset_formula (t : ℕ) (ht : t ≤ T) : tr.live t ⊆ tr.formula t := by
  induction t with
  | zero => simp
  | succ t ih =>
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact (Finset.mem_inter.mp hC).2
    · exact tr.inserted_live t (by omega) hC

theorem live_nonempty (t : ℕ) (ht : t ≤ T) :
    ∀ C ∈ tr.live t, C.Nonempty := by
  induction t with
  | zero => simp
  | succ t ih =>
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact ih (by omega) C (Finset.mem_inter.mp hC).1
    · exact tr.inserted_nonempty t (by omega) C hC

/-- Every tracked clause has a genuine earlier insertion event. -/
theorem live_has_origin {t : ℕ} {C : Finset α} (hC : C ∈ tr.live t) :
    ∃ s < t, C ∈ tr.inserted s := by
  induction t with
  | zero => simp at hC
  | succ t ih =>
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨s, hs, hCs⟩ := ih (Finset.mem_inter.mp hC).1
      exact ⟨s, by omega, hCs⟩
    · exact ⟨t, Nat.lt_succ_self _, hC⟩

/-- The absorbing subset is inserted strictly after the removed clause's
original insertion event, even though absorption and subset insertion share
the same replacement step. -/
theorem removed_has_later_subset {t : ℕ} (ht : t < T)
    {C : Finset α} (hC : C ∈ tr.removed t) :
    ∃ s < t, C ∈ tr.inserted s ∧ ∃ Q ∈ tr.inserted t, Q ⊂ C := by
  obtain ⟨hCL, hCF⟩ := Finset.mem_sdiff.mp hC
  obtain ⟨s, hs, hCs⟩ := tr.live_has_origin hCL
  exact ⟨s, hs, hCs,
    tr.removed_subset t ht C (tr.live_subset_formula t (by omega) hCL) hCF⟩

theorem removed_has_subset {t : ℕ} (ht : t < T)
    {C : Finset α} (hC : C ∈ tr.removed t) :
    ∃ Q ∈ tr.inserted t, Q ⊂ C := by
  obtain ⟨s, hs, hCs, hQ⟩ := tr.removed_has_later_subset ht hC
  exact hQ

/-- The one-step conservation law for insertion events. -/
theorem accounting_step (t j : ℕ) (ht : t < T) :
    widthCount (tr.live (t + 1)) j + widthCount (tr.removed t) j =
      widthCount (tr.live t) j + widthCount (tr.inserted t) j := by
  let A := (tr.live t).filter fun C => C.card = j
  let B := (tr.inserted t).filter fun C => C.card = j
  have hsplit : (tr.live (t + 1)).filter (fun C => C.card = j) =
      (A ∩ tr.formula (t + 1)) ∪ B := by
    ext C
    simp only [live_succ, Finset.mem_filter, Finset.mem_union, Finset.mem_inter, A, B]
    tauto
  have hremoved : (tr.removed t).filter (fun C => C.card = j) =
      A \ tr.formula (t + 1) := by
    ext C
    simp only [removed, Finset.mem_filter, Finset.mem_sdiff, A]
    tauto
  have hd : Disjoint (A ∩ tr.formula (t + 1)) B := by
    apply Finset.disjoint_left.mpr
    intro C hCA hCB
    have hCF : C ∈ tr.formula t := tr.live_subset_formula t (by omega)
      (Finset.mem_filter.mp (Finset.mem_inter.mp hCA).1).1
    exact Finset.disjoint_left.mp (tr.fresh t ht) hCF (Finset.mem_filter.mp hCB).1
  have hp := Finset.card_sdiff_add_card_inter A (tr.formula (t + 1))
  change ((tr.live (t + 1)).filter _).card + ((tr.removed t).filter _).card =
    A.card + B.card
  rw [hsplit, hremoved, Finset.card_union_of_disjoint hd]
  omega

/-- Telescoping counts insertions by their fate: still live or removed once.
This remains valid even without a no-reinsertion theorem. -/
theorem accounting (t j : ℕ) (ht : t ≤ T) :
    tr.insertions t j = widthCount (tr.live t) j + tr.removals t j := by
  induction t with
  | zero => simp [insertions, removals, widthCount]
  | succ t ih =>
    have hi := ih (by omega)
    have hs := tr.accounting_step t j (by omega)
    simp only [insertions, removals, Finset.sum_range_succ] at hi ⊢
    omega

theorem insertions_zero : tr.insertions T 0 = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro Q hQ hcard
  have hp := (tr.inserted_nonempty t (Finset.mem_range.mp ht) Q hQ).card_pos
  omega

end Trace

section SATLiteralUniverse

variable {V : Type*} [DecidableEq V] [Fintype V] {T : ℕ}

theorem mem_literalUniverse (l : SAT.Literal V) : l ∈ literalUniverse (V := V) := by
  apply Finset.mem_image.mpr
  refine ⟨(l.variable, l.positive), Finset.mem_univ _, ?_⟩
  cases l
  rfl

theorem literalUniverse_card_le : (literalUniverse (V := V)).card ≤
    2 * Fintype.card V := by
  calc
    (literalUniverse (V := V)).card ≤ (Finset.univ : Finset (V × Bool)).card :=
      Finset.card_image_le
    _ = 2 * Fintype.card V := by simp [Nat.mul_comm]

end SATLiteralUniverse

end SubexponentialSAT.RemovalCharging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFCodeTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact list transport through literal codes

These equalities preserve clause order and the last-occurrence conventions.
They connect the encoded normalization programs to the typed executable CNF
operations, rather than identifying only their finite-set semantics.
-/

namespace SubexponentialSAT.ExecCNFCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

theorem petal_filter_set (C H : Clause α) :
    clauseSet (C.filter (fun x => !decide (x ∈ H))) = clauseSet C \ clauseSet H := by
  ext x
  simp [clauseSet]

theorem petal_family_set (G : Formula α) (H : Clause α) :
    formulaSet (G.map (fun C => C.filter (fun x => !decide (x ∈ H)))) =
      (formulaSet G).image (fun C => C \ clauseSet H) := by
  ext D
  constructor
  · intro hD
    obtain ⟨C, hC, he⟩ := mem_formulaSet.mp hD
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hC
    exact Finset.mem_image.mpr ⟨clauseSet A, mem_formulaSet.mpr ⟨A, hA, rfl⟩,
      (petal_filter_set A H).symm.trans he⟩
  · intro hD
    obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hD
    obtain ⟨A, hA, rfl⟩ := mem_formulaSet.mp hC
    exact mem_formulaSet.mpr ⟨A.filter (fun x => !decide (x ∈ H)),
      List.mem_map.mpr ⟨A, hA, rfl⟩, (petal_filter_set A H).trans he⟩

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


/-- Set semantics of the exact list output, valid even with reordered or
repeated literals and repeated clauses in any of the supplied lists. -/
theorem result_set {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) :
    ExecCNF.formulaSet (result F selected H) =
      (insert (ExecCNF.clauseSet H) (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected)).filter
        (fun C => ¬ ∃ D ∈ insert (ExecCNF.clauseSet H)
          (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected), D ⊂ C) := by
  simp only [result, ExecCNF.formulaSet_absorb, ExecCNF.formulaSet_cons,
    ExecCNF.formulaSet_eraseClauses]

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual construction of the petal child. The core, selected family, and
parent occupy the same three ports as the core-child program. -/
namespace SubexponentialSAT.ExecPetalChildProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

theorem petals_set {α : Type*} [DecidableEq α] (selected : List (List α)) (H : List α) :
    ExecCNF.formulaSet (petals selected H) =
      (ExecCNF.formulaSet selected).image (fun C => C \ ExecCNF.clauseSet H) :=
  ExecCNFCodeTransport.petal_family_set selected H

theorem result_set {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) :
    let P := (ExecCNF.formulaSet selected).image (fun C => C \ ExecCNF.clauseSet H)
    let G := P ∪ (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected)
    ExecCNF.formulaSet (result F selected H) = G.filter (fun C => ¬ ∃ D ∈ G, D ⊂ C) := by
  simp only [result, ExecCNF.formulaSet_absorb, ExecCNF.formulaSet_append,
    ExecCNF.formulaSet_eraseClauses, petals_set]

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CNFNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Raw input normalization for the frozen counting manuscript, lines 1758–1762.
The ambient type remains `Fin n` throughout, including unused variables.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

variable {n : ℕ}

theorem formulaSet_width_le (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) : SAT.WidthAtMost k (ExecCNF.formulaSet F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  exact D.toFinset_card_le.trans (h D hD)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsify
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: literal-core branching with disjoint exact-count children. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch

open OAI.Algorithms.SubexponentialSAT.SAT

universe u
variable {V : Type u} [DecidableEq V]

theorem sdiff_injOn_selected (F : CNF V) (c : ℕ) (H : Clause V) :
    Set.InjOn (fun C => C \ H) (selected F c H) :=
  SunflowerBranch.sdiff_injective_on fun _ hC => (mem_selected.mp hC).2.2

theorem petals_card (F : CNF V) (c : ℕ) (H : Clause V) :
    (petals F c H).card = (selected F c H).card :=
  Finset.card_image_of_injOn (sdiff_injOn_selected F c H)

theorem petals_filter_card (F : CNF V) (c : ℕ) (H S : Clause V)
    (hHS : Disjoint H S) :
    ((petals F c H).filter fun P => S ⊆ P).card =
      (selected F c (H ∪ S)).card := by
  have hfilter : (selected F c H).filter (fun C => S ⊆ C \ H) =
      selected F c (H ∪ S) := by
    ext C
    simp [selected, Finset.subset_sdiff, Finset.union_subset_iff, hHS.symm, and_assoc]
  unfold petals SunflowerBranch.petalFamily
  rw [Finset.filter_image, hfilter]
  exact Finset.card_image_of_injOn (SunflowerBranch.sdiff_injective_on fun C hC =>
    Finset.subset_union_left.trans (mem_selected.mp hC).2.2)

theorem selected_card_le_insertedB_width {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty) :
    (selected F c H).card ≤ ((insertedB F c H).filter
      fun P => P.card = c - H.card).card := by
  rw [← petals_card]
  apply Finset.card_le_card
  intro P hP
  exact Finset.mem_filter.mpr ⟨petals_subset_insertedB hF hH hP, petal_card hP⟩

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriority
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: smallest-width, largest-core selection and marked degrees. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority

open OAI.Algorithms.SubexponentialSAT.SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

theorem degree_mono {V : Type*} [DecidableEq V] {F G : CNF V}
    (hFG : F ⊆ G) (j : ℕ) (S : Clause V) : degree F j S ≤ degree G j S := by
  apply Finset.card_le_card
  intro C hC
  exact mem_selected.mpr ⟨hFG (mem_selected.mp hC).1, (mem_selected.mp hC).2⟩

theorem degree_union_le {V : Type*} [DecidableEq V] (F G : CNF V)
    (j : ℕ) (S : Clause V) : degree (F ∪ G) j S ≤ degree F j S + degree G j S := by
  unfold degree selected
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

private theorem degree_eq_zero_of_width {V : Type*} [DecidableEq V]
    {F : CNF V} {j : ℕ} (S : Clause V) (hF : ∀ C ∈ F, C.card ≠ j) :
    degree F j S = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  exact hF C (mem_selected.mp hC).1 (mem_selected.mp hC).2.1

theorem Priority.petals_degree_lt {F : CNF (Fin n)} {M c : ℕ} {H S : Clause (Fin n)}
    (hM : 0 < M) (h : Priority F M c H)
    (hS : 0 < S.card) (hSj : S.card < c - H.card) :
    degree (petals F c H) (c - H.card) S < M ^ (c - H.card - S.card) := by
  by_cases hzero : degree (petals F c H) (c - H.card) S = 0
  · rw [hzero]
    exact pow_pos hM _
  have hpos : 0 < (selected (petals F c H) (c - H.card) S).card :=
    Nat.pos_of_ne_zero hzero
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  obtain ⟨hP, _, hSP⟩ := mem_selected.mp hP
  obtain ⟨C, _, hCP⟩ := Finset.mem_image.mp hP
  have hHS : Disjoint H S := by
    apply Finset.disjoint_left.mpr
    intro l hlH hlS
    have hlP := hSP hlS
    rw [← hCP] at hlP
    exact (Finset.mem_sdiff.mp hlP).2 hlH
  have hcard : (H ∪ S).card = H.card + S.card := Finset.card_union_of_disjoint hHS
  have hHc := h.core_proper
  have hlarge := h.maximum (H ∪ S)
    (by omega) (by omega)
  have heq : selected (petals F c H) (c - H.card) S =
      (petals F c H).filter (fun P => S ⊆ P) := by
    ext P
    simp only [mem_selected, Finset.mem_filter]
    constructor
    · rintro ⟨hP, _, hSP⟩
      exact ⟨hP, hSP⟩
    · rintro ⟨hP, hSP⟩
      exact ⟨hP, petal_card hP, hSP⟩
  unfold degree at hlarge ⊢
  rw [heq, petals_filter_card F c H S hHS]
  simpa [hcard, Nat.sub_sub] using hlarge

/-- A marked `A` child may discard clauses; adding its single core preserves the bound. -/
theorem Priority.marked_degree_childA {F marked next : CNF (Fin n)} {M c j : ℕ}
    {H S : Clause (Fin n)} (hM : 2 ≤ M) (h : Priority F M c H)
    (hmarked : marked ⊆ F) (hnext : next ⊆ marked ∪ {H})
    (hS : 0 < S.card) (hSj : S.card < j)
    (hold : degree marked j S < 2 * M ^ (j - S.card)) :
    degree next j S < 2 * M ^ (j - S.card) := by
  have hcap := (degree_mono hnext j S).trans (degree_union_le marked {H} j S)
  by_cases hHj : H.card = j
  · have hsmall := h.minimum S hS hSj (by have hc := h.core_proper; omega)
    have hmarked' := degree_mono hmarked j S
    have hsingle : degree ({H} : CNF (Fin n)) j S ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hpow : 1 < M ^ (j - S.card) :=
      Nat.one_lt_pow (Nat.sub_ne_zero_of_lt hSj) hM
    omega
  · have hzero : degree ({H} : CNF (Fin n)) j S = 0 :=
      degree_eq_zero_of_width S (by simpa using hHj)
    omega

/-- Petals and false-core units preserve the bound at every marked `B` child. -/
theorem Priority.marked_degree_childB {F marked next : CNF (Fin n)} {M c j : ℕ}
    {H S : Clause (Fin n)} (hM : 2 ≤ M) (h : Priority F M c H)
    (hmarked : marked ⊆ F)
    (hnext : next ⊆ (marked ∪ petals F c H) ∪ negatedCoreUnits H)
    (hS : 0 < S.card) (hSj : S.card < j)
    (hold : degree marked j S < 2 * M ^ (j - S.card)) :
    degree next j S < 2 * M ^ (j - S.card) := by
  have hunits : degree (negatedCoreUnits H) j S = 0 := by
    apply degree_eq_zero_of_width S
    intro C hC
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hC
    simp only [Finset.card_singleton]
    omega
  have hcap := (degree_mono hnext j S).trans
    ((degree_union_le (marked ∪ petals F c H) (negatedCoreUnits H) j S).trans
      (Nat.add_le_add_right (degree_union_le marked (petals F c H) j S) _))
  by_cases hj : j = c - H.card
  · have hHc := h.core_nonempty
    have hsmall := h.minimum S hS hSj (by omega)
    have hmarked' := degree_mono hmarked j S
    have hpetals := h.petals_degree_lt (by omega) hS (by omega)
    rw [← hj] at hpetals
    omega
  · have hzero : degree (petals F c H) j S = 0 := by
      apply degree_eq_zero_of_width S
      intro P hP heq
      have hp := petal_card hP
      omega
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCharging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A, insertion recurrence and the resulting path budgets. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging

open scoped BigOperators

section FiniteCharging

variable {α : Type*} [DecidableEq α]

/-- Charge each removed marked clause to an inserted strict subset. Fibers may
overlap; their width-sensitive bounds are precisely those from marked priority. -/
theorem removed_card_le (marked removed inserted : Finset (Finset α)) (j M : ℕ)
    (hremoved : removed ⊆ marked)
    (hnonempty : ∀ Q ∈ inserted, Q.Nonempty)
    (hcharge : ∀ C ∈ removed, ∃ Q ∈ inserted, Q ⊂ C)
    (hdegree : ∀ Q ∈ inserted, 0 < Q.card → Q.card < j →
      (marked.filter fun C => C.card = j ∧ Q ⊆ C).card ≤ 2 * M ^ (j - Q.card)) :
    (removed.filter fun C => C.card = j).card ≤
      2 * ∑ i ∈ Finset.range j,
        M ^ (j - i) * (inserted.filter fun Q => Q.card = i).card := by
  let s := removed.filter fun C => C.card = j
  let t := inserted.filter fun Q => Q.card < j
  have hcover : s ⊆ t.biUnion (fun Q => s.filter fun C => Q ⊆ C) := by
    intro C hC
    obtain ⟨hCR, hCj⟩ := Finset.mem_filter.mp hC
    obtain ⟨Q, hQI, hQC⟩ := hcharge C hCR
    apply Finset.mem_biUnion.mpr
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQI, hCj ▸ Finset.card_lt_card hQC⟩,
      Finset.mem_filter.mpr ⟨hC, (Finset.ssubset_iff_subset_ne.mp hQC).1⟩⟩
  have hfiber : ∀ Q ∈ t, (s.filter fun C => Q ⊆ C).card ≤ 2 * M ^ (j - Q.card) := by
    intro Q hQ
    obtain ⟨hQI, hQj⟩ := Finset.mem_filter.mp hQ
    apply le_trans _ (hdegree Q hQI (hnonempty Q hQI).card_pos hQj)
    apply Finset.card_le_card
    intro C hC
    obtain ⟨hCs, hQC⟩ := Finset.mem_filter.mp hC
    obtain ⟨hCR, hCj⟩ := Finset.mem_filter.mp hCs
    exact Finset.mem_filter.mpr ⟨hremoved hCR, hCj, hQC⟩
  calc
    s.card ≤ (t.biUnion fun Q => s.filter fun C => Q ⊆ C).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ Q ∈ t, (s.filter fun C => Q ⊆ C).card := Finset.card_biUnion_le
    _ ≤ ∑ Q ∈ t, 2 * M ^ (j - Q.card) := Finset.sum_le_sum hfiber
    _ = 2 * ∑ i ∈ Finset.range j,
        M ^ (j - i) * (inserted.filter fun Q => Q.card = i).card := by
      have h := Finset.sum_fiberwise_eq_sum_filter' inserted (Finset.range j)
        Finset.card (fun i => 2 * M ^ (j - i))
      simp only [Finset.mem_range] at h
      change (∑ Q ∈ inserted.filter (fun Q => Q.card < j), 2 * M ^ (j - Q.card)) = _
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_assoc, mul_comm, mul_left_comm]

end FiniteCharging

/-- The recurrence in source equation `spar-insertions`, indexed from width one. -/
theorem insertion_le (M n k : ℕ) (N : ℕ → ℕ)
    (hrec : ∀ j < k - 1,
      N (j + 1) ≤ 4 * n * M ^ j +
        2 * ∑ i ∈ Finset.range j, M ^ (j - i) * N (i + 1)) :
    ∀ j < k - 1, N (j + 1) ≤ 4 * (3 * M) ^ j * n := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have hsum : (∑ i ∈ Finset.range j, M ^ (j - i) * N (i + 1)) ≤
        4 * n * M ^ j * ∑ i ∈ Finset.range j, 3 ^ i := by
      calc
        _ ≤ ∑ i ∈ Finset.range j, M ^ (j - i) * (4 * (3 * M) ^ i * n) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Nat.mul_le_mul_left _
            (ih i (Finset.mem_range.mp hi) ((Finset.mem_range.mp hi).trans hj))
        _ = 4 * n * M ^ j * ∑ i ∈ Finset.range j, 3 ^ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hpow : M ^ (j - i) * M ^ i = M ^ j := by
            rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt (Finset.mem_range.mp hi))]
          rw [mul_pow]
          calc
            _ = 4 * n * (M ^ (j - i) * M ^ i) * 3 ^ i := by ring
            _ = _ := by rw [hpow]
    have hgeom : (∑ i ∈ Finset.range j, 3 ^ i) * 2 + 1 = 3 ^ j :=
      geom_sum_mul_add (2 : ℕ) j
    calc
      N (j + 1) ≤ 4 * n * M ^ j +
          2 * ∑ i ∈ Finset.range j, M ^ (j - i) * N (i + 1) := hrec j hj
      _ ≤ 4 * n * M ^ j +
          2 * (4 * n * M ^ j * ∑ i ∈ Finset.range j, 3 ^ i) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 2 hsum) _
      _ = 4 * n * M ^ j * ((∑ i ∈ Finset.range j, 3 ^ i) * 2 + 1) := by ring
      _ = 4 * (3 * M) ^ j * n := by rw [hgeom, mul_pow]; ring

/-- Every edge inserts at least one clause; summing the sharp per-width bounds
therefore bounds a path's number of edges. -/
theorem depth_le (M n k T : ℕ) (N : ℕ → ℕ)
    (hsteps : T ≤ ∑ j ∈ Finset.range (k - 1), N (j + 1))
    (hN : ∀ j < k - 1, N (j + 1) ≤ 4 * (3 * M) ^ j * n) :
    T ≤ depthConstant k M * n := by
  calc
    T ≤ ∑ j ∈ Finset.range (k - 1), N (j + 1) := hsteps
    _ ≤ ∑ j ∈ Finset.range (k - 1), 4 * (3 * M) ^ j * n :=
      Finset.sum_le_sum fun j hj => hN j (Finset.mem_range.mp hj)
    _ = depthConstant k M * n := by
      simp only [depthConstant, ← Finset.sum_mul, ← Finset.mul_sum]

/-- Count B-edges by their petal width. The integral multiplicative form
retains the exact bound without truncating division. -/
theorem right_steps_mul_le (M n k : ℕ) (hM : 0 < M) (b : ℕ → ℕ)
    (hinsert : ∀ j < k - 1, b j * M ^ (j + 1) ≤ 4 * (3 * M) ^ j * n) :
    (∑ j ∈ Finset.range (k - 1), b j) * M ≤ rightConstant k * n := by
  have hwidth : ∀ j < k - 1, b j * M ≤ 4 * 3 ^ j * n := by
    intro j hj
    apply Nat.le_of_mul_le_mul_right (c := M ^ j) _ (pow_pos hM j)
    simpa [pow_succ, mul_pow, mul_assoc, mul_comm, mul_left_comm] using hinsert j hj
  calc
    (∑ j ∈ Finset.range (k - 1), b j) * M =
        ∑ j ∈ Finset.range (k - 1), b j * M := Finset.sum_mul _ _ _
    _ ≤ ∑ j ∈ Finset.range (k - 1), 4 * 3 ^ j * n :=
      Finset.sum_le_sum fun j hj => hwidth j (Finset.mem_range.mp hj)
    _ = rightConstant k * n := by
      simp only [rightConstant, ← Finset.sum_mul, ← Finset.mul_sum]

section Trace

open RemovalCharging

variable {α : Type*} [DecidableEq α] {T : ℕ}

/-- Count actual edges by their insertion events, grouped by positive width. -/
theorem trace_steps_le_insertions (tr : Trace α T) (k : ℕ)
    (hbatch : ∀ t < T, (tr.inserted t).Nonempty)
    (hwidth : ∀ t < T, ∀ C ∈ tr.inserted t, C.card < k) :
    T ≤ ∑ j ∈ Finset.range (k - 1), tr.insertions T (j + 1) := by
  have hsplit : ∀ t < T, (∑ j ∈ Finset.range (k - 1),
      widthCount (tr.inserted t) (j + 1)) = (tr.inserted t).card := by
    intro t ht
    calc
      _ = ∑ j ∈ Finset.Ico 1 k, widthCount (tr.inserted t) j := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp [Nat.add_comm]
      _ = ((tr.inserted t).filter fun C => C.card ∈ Finset.Ico 1 k).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ = (tr.inserted t).card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro C hC
        exact Finset.mem_Ico.mpr
          ⟨(tr.inserted_nonempty t ht C hC).card_pos, hwidth t ht C hC⟩
  calc
    T = ∑ _t ∈ Finset.range T, 1 := by simp
    _ ≤ ∑ t ∈ Finset.range T, (tr.inserted t).card :=
      Finset.sum_le_sum fun t ht => (hbatch t (Finset.mem_range.mp ht)).card_pos
    _ = ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range (k - 1),
        widthCount (tr.inserted t) (j + 1) :=
      Finset.sum_congr rfl fun t ht => (hsplit t (Finset.mem_range.mp ht)).symm
    _ = ∑ j ∈ Finset.range (k - 1), tr.insertions T (j + 1) := by
      rw [Finset.sum_comm]
      rfl

/-- Nonempty strict-subset replacements never remove an inserted unit clause. -/
theorem trace_units_le (tr : Trace α T) (U : Finset α)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U) : tr.insertions T 1 ≤ U.card := by
  have hremoved : tr.removals T 1 = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro C hC
    obtain ⟨hCR, hC1⟩ := Finset.mem_filter.mp hC
    obtain ⟨Q, hQI, hQC⟩ := tr.removed_has_subset (Finset.mem_range.mp ht) hCR
    have hpos := (tr.inserted_nonempty t (Finset.mem_range.mp ht) Q hQI).card_pos
    have hlt := Finset.card_lt_card hQC
    omega
  rw [tr.accounting T 1 le_rfl, hremoved, Nat.add_zero]
  have hdeg : ∀ a, widthLiteralDegree (tr.live T) 1 a ≤ 1 := by
    intro a
    calc
      _ ≤ ({({a} : Finset α)} : Finset (Finset α)).card := by
        apply Finset.card_le_card
        intro C hC
        obtain ⟨_, hC1, ha⟩ := Finset.mem_filter.mp hC
        obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hC1
        have hab : a = b := Finset.mem_singleton.mp ha
        simp [hab]
      _ = 1 := Finset.card_singleton _
  simpa using widthCount_le_universe_mul (tr.live T) U 1 1
    (tr.live_nonempty T le_rfl) hsupport hdeg

/-- Equation `spar-insertions` for the actual insertion and removal events of
a finite path; the marked-degree hypothesis is supplied by priority. -/
theorem trace_insertion_recurrence (tr : Trace α T) (M n k : ℕ) (U : Finset α)
    (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hdegree : ∀ t ≤ T, ∀ j < k, ∀ S : Finset α, 0 < S.card → S.card < j →
      ((tr.live t).filter fun C => C.card = j ∧ S ⊆ C).card ≤
        2 * M ^ (j - S.card)) :
    ∀ q < k - 1, tr.insertions T (q + 1) ≤ 4 * n * M ^ q +
      2 * ∑ i ∈ Finset.range q, M ^ (q - i) * tr.insertions T (i + 1) := by
  intro q hq
  cases q with
  | zero =>
    have hu := (trace_units_le tr U hsupport).trans hU
    simpa using hu.trans (show 2 * n ≤ 4 * n by omega)
  | succ q =>
    have hj : q + 1 + 1 < k := by omega
    have hfinal : widthCount (tr.live T) (q + 1 + 1) ≤
        4 * n * M ^ (q + 1) := by
      have hdeg : ∀ a, widthLiteralDegree (tr.live T) (q + 1 + 1) a ≤
          2 * M ^ (q + 1) := by
        intro a
        simpa [widthLiteralDegree] using
          hdegree T le_rfl (q + 1 + 1) hj {a} (by simp) (by simp)
      calc
        _ ≤ (2 * M ^ (q + 1)) * U.card :=
          widthCount_le_universe_mul (tr.live T) U _ _
            (tr.live_nonempty T le_rfl) hsupport hdeg
        _ ≤ (2 * M ^ (q + 1)) * (2 * n) := Nat.mul_le_mul_left _ hU
        _ = 4 * n * M ^ (q + 1) := by ring
    have hrem : tr.removals T (q + 1 + 1) ≤
        2 * ∑ i ∈ Finset.range (q + 1 + 1),
          M ^ (q + 1 + 1 - i) * tr.insertions T i := by
      calc
        _ ≤ ∑ t ∈ Finset.range T,
            2 * ∑ i ∈ Finset.range (q + 1 + 1),
              M ^ (q + 1 + 1 - i) * widthCount (tr.inserted t) i := by
          apply Finset.sum_le_sum
          intro t ht
          apply removed_card_le (tr.live t) (tr.removed t) (tr.inserted t)
          · exact Finset.sdiff_subset
          · exact tr.inserted_nonempty t (Finset.mem_range.mp ht)
          · intro C hC
            exact tr.removed_has_subset (Finset.mem_range.mp ht) hC
          · intro S _ hS hSj
            exact hdegree t (Nat.le_of_lt (Finset.mem_range.mp ht)) _ hj S hS hSj
        _ = 2 * ∑ i ∈ Finset.range (q + 1 + 1),
            M ^ (q + 1 + 1 - i) * tr.insertions T i := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Trace.insertions, Finset.mul_sum]
    rw [Finset.sum_range_succ'] at hrem
    simp only [tr.insertions_zero, Nat.mul_zero, Nat.add_zero,
      Nat.add_sub_add_right] at hrem
    rw [tr.accounting T (q + 1 + 1) le_rfl]
    exact Nat.add_le_add hfinal hrem

/-- The sharp source bound, now applied to an actual finite replacement trace. -/
theorem trace_insertions_le (tr : Trace α T) (M n k : ℕ) (U : Finset α)
    (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hdegree : ∀ t ≤ T, ∀ j < k, ∀ S : Finset α, 0 < S.card → S.card < j →
      ((tr.live t).filter fun C => C.card = j ∧ S ⊆ C).card ≤
        2 * M ^ (j - S.card)) :
    ∀ j < k - 1, tr.insertions T (j + 1) ≤ 4 * (3 * M) ^ j * n :=
  insertion_le M n k (tr.insertions T)
    (trace_insertion_recurrence tr M n k U hU hsupport hdegree)

/-- The source depth bound counts every edge of the same concrete path. -/
theorem trace_depth_le (tr : Trace α T) (M n k : ℕ) (U : Finset α)
    (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hbatch : ∀ t < T, (tr.inserted t).Nonempty)
    (hwidth : ∀ t < T, ∀ C ∈ tr.inserted t, C.card < k)
    (hdegree : ∀ t ≤ T, ∀ j < k, ∀ S : Finset α, 0 < S.card → S.card < j →
      ((tr.live t).filter fun C => C.card = j ∧ S ⊆ C).card ≤
        2 * M ^ (j - S.card)) :
    T ≤ depthConstant k M * n :=
  depth_le M n k T (tr.insertions T) (trace_steps_le_insertions tr k hbatch hwidth)
    (trace_insertions_le tr M n k U hU hsupport hdegree)

/-- A B-edge of petal width `w` consumes at least `M^w` actual insertion events. -/
theorem trace_right_steps_mul_le (tr : Trace α T) (M n k : ℕ) (hM : 0 < M)
    (U : Finset α) (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hdegree : ∀ t ≤ T, ∀ j < k, ∀ S : Finset α, 0 < S.card → S.card < j →
      ((tr.live t).filter fun C => C.card = j ∧ S ⊆ C).card ≤
        2 * M ^ (j - S.card))
    (b : ℕ → Bool) (w : ℕ → ℕ)
    (hwidth : ∀ t < T, b t = true → 0 < w t ∧ w t < k)
    (hbatch : ∀ t < T, b t = true → M ^ w t ≤ widthCount (tr.inserted t) (w t)) :
    ((Finset.range T).filter fun t => b t = true).card * M ≤ rightConstant k * n := by
  let R := (Finset.range T).filter fun t => b t = true
  let counts := fun j => (R.filter fun t => w t = j + 1).card
  have hsplit : R.card = ∑ j ∈ Finset.range (k - 1), counts j := by
    symm
    calc
      _ = ∑ j ∈ Finset.Ico 1 k, (R.filter fun t => w t = j).card := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp [counts, Nat.add_comm]
      _ = (R.filter fun t => w t ∈ Finset.Ico 1 k).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ = R.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro t ht
        obtain ⟨ht, hb⟩ := Finset.mem_filter.mp ht
        exact Finset.mem_Ico.mpr (hwidth t (Finset.mem_range.mp ht) hb)
  change R.card * M ≤ rightConstant k * n
  rw [hsplit]
  apply right_steps_mul_le M n k hM counts
  intro j hj
  apply le_trans _ (trace_insertions_le tr M n k U hU hsupport hdegree j hj)
  calc
    counts j * M ^ (j + 1) = ∑ t ∈ R.filter (fun t => w t = j + 1),
        M ^ (j + 1) := by simp [counts]
    _ ≤ ∑ t ∈ R.filter (fun t => w t = j + 1),
        widthCount (tr.inserted t) (j + 1) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨htR, hw⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht, hb⟩ := Finset.mem_filter.mp htR
      simpa only [hw] using hbatch t (Finset.mem_range.mp ht) hb
    _ ≤ ∑ t ∈ Finset.range T, widthCount (tr.inserted t) (j + 1) :=
      Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))

end Trace

section SelectedTrace

open RemovalCharging DisjointBranch

variable {n T : ℕ}

/-- Priority bounds marked subset degrees at every prefix of a selected path. -/
theorem trace_marked_degree (tr : Trace (SAT.Literal (Fin n)) T) (M : ℕ)
    (hM : 2 ≤ M)
    (hstep : ∀ t < T, ∃ c H,
      SparsePriority.Priority (tr.formula t) M c H ∧
        (tr.inserted t = {H} ∨ tr.inserted t = insertedB (tr.formula t) c H)) :
    ∀ t ≤ T, ∀ (j : ℕ) (S : SAT.Clause (Fin n)), 0 < S.card → S.card < j →
      SparsePriority.degree (tr.live t) j S < 2 * M ^ (j - S.card) := by
  intro t ht
  induction t with
  | zero =>
    intro j S _ _
    change (selected ∅ j S).card < 2 * M ^ (j - S.card)
    simp only [selected, Finset.filter_empty, Finset.card_empty]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  | succ t ih =>
    intro j S hS hSj
    have htT : t < T := by omega
    obtain ⟨c, H, hsel, hA | hB⟩ := hstep t htT
    · apply SparsePriority.Priority.marked_degree_childA hM hsel
        (tr.live_subset_formula t (by omega))
      · intro C hC
        rcases Finset.mem_union.mp hC with hC | hC
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hC).1)
        · exact Finset.mem_union.mpr (Or.inr (hA ▸ hC))
      · exact hS
      · exact hSj
      · exact ih (by omega) j S hS hSj
    · apply SparsePriority.Priority.marked_degree_childB hM hsel
        (tr.live_subset_formula t (by omega))
      · intro C hC
        rcases Finset.mem_union.mp hC with hC | hC
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hC).1)))
        · rw [hB] at hC
          rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hC).1 with hP | hU
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hP)))
          · exact Finset.mem_union.mpr (Or.inr hU)
      · exact hS
      · exact hSj
      · exact ih (by omega) j S hS hSj

/-- Every actual selected path has the draft's linear depth bound. -/
theorem selected_path_depth_le (F : ℕ → SAT.CNF (Fin n)) (c : ℕ → ℕ)
    (H : ℕ → SAT.Clause (Fin n)) (b : ℕ → Bool) (M k : ℕ) (hM : 2 ≤ M)
    (hselect : ∀ t < T, SparsePriority.Priority (F t) M (c t) (H t))
    (hnext : ∀ t < T, F (t + 1) =
      if b t then childB (F t) (c t) (H t) else childA (F t) (c t) (H t))
    (hanti : SunflowerBranch.Antichain (F 0))
    (hnt : ∀ C ∈ F 0, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k (F 0)) :
    T ≤ depthConstant k M * n := by
  let tr := selectedTrace F c H b M k hselect hnext hanti hnt hwidth
  have hstep : ∀ t < T, ∃ c H,
      SparsePriority.Priority (tr.formula t) M c H ∧
        (tr.inserted t = {H} ∨ tr.inserted t = insertedB (tr.formula t) c H) := by
    intro t ht
    refine ⟨c t, H t, hselect t ht, ?_⟩
    cases hb : b t <;> simp [tr, selectedTrace, hb]
  apply trace_depth_le tr M n k (literalUniverse (V := Fin n))
  · simpa using (literalUniverse_card_le (V := Fin n))
  · intro C _ a _
    exact mem_literalUniverse a
  · intro t ht
    have hs := (hselect t ht).spec
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    change (if b t then insertedB (F t) (c t) (H t) else {H t}).Nonempty
    cases hb : b t
    · simp
    · simp only [↓reduceIte]
      obtain ⟨C, hCF, hCc, hHC⟩ := hs.1
      refine ⟨C \ H t, petals_subset_insertedB hinv.1 (Finset.card_pos.mp hs.2.1) ?_⟩
      exact Finset.mem_image.mpr ⟨C, mem_selected.mpr ⟨hCF, hCc, hHC⟩, rfl⟩
  · intro t ht Q hQ
    have hs := (hselect t ht).spec
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    obtain ⟨C, hCF, hCc, _⟩ := hs.1
    have hck : c t ≤ k := hCc ▸ hinv.2.2 C hCF
    change Q ∈ (if b t then insertedB (F t) (c t) (H t) else {H t}) at hQ
    cases hb : b t <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hQ
    · rw [Finset.mem_singleton.mp hQ]
      exact hs.2.2.1.trans_le hck
    · exact (insertedB_width_lt (Finset.card_pos.mp hs.2.1) hs.2.2.1 hQ).trans_le hck
  · intro t ht j _ S hS hSj
    simpa [SparsePriority.degree, selected] using
      (trace_marked_degree tr M hM hstep t ht j S hS hSj).le

/-- The B-choice bound for the same actual selected path. -/
theorem selected_path_right_steps_mul_le (F : ℕ → SAT.CNF (Fin n)) (c : ℕ → ℕ)
    (H : ℕ → SAT.Clause (Fin n)) (b : ℕ → Bool) (M k : ℕ) (hM : 2 ≤ M)
    (hselect : ∀ t < T, SparsePriority.Priority (F t) M (c t) (H t))
    (hnext : ∀ t < T, F (t + 1) =
      if b t then childB (F t) (c t) (H t) else childA (F t) (c t) (H t))
    (hanti : SunflowerBranch.Antichain (F 0))
    (hnt : ∀ C ∈ F 0, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k (F 0)) :
    ((Finset.range T).filter fun t => b t = true).card * M ≤ rightConstant k * n := by
  let tr := selectedTrace F c H b M k hselect hnext hanti hnt hwidth
  have hstep : ∀ t < T, ∃ c H,
      SparsePriority.Priority (tr.formula t) M c H ∧
        (tr.inserted t = {H} ∨ tr.inserted t = insertedB (tr.formula t) c H) := by
    intro t ht
    refine ⟨c t, H t, hselect t ht, ?_⟩
    cases hb : b t <;> simp [tr, selectedTrace, hb]
  refine trace_right_steps_mul_le tr M n k (by omega) (literalUniverse (V := Fin n))
      ?_ ?_ ?_ b (fun t => c t - (H t).card) ?_ ?_
  · simpa using (literalUniverse_card_le (V := Fin n))
  · intro C _ a _
    exact mem_literalUniverse a
  · intro t ht j _ S hS hSj
    simpa [SparsePriority.degree, selected] using
      (trace_marked_degree tr M hM hstep t ht j S hS hSj).le
  · intro t ht _
    have hs := (hselect t ht).spec
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    obtain ⟨C, hCF, hCc, _⟩ := hs.1
    have hck : c t ≤ k := hCc ▸ hinv.2.2 C hCF
    exact ⟨Nat.sub_pos_of_lt hs.2.2.1,
      (Nat.sub_lt (hs.2.1.trans hs.2.2.1) hs.2.1).trans_le hck⟩
  · intro t ht hb
    have hs := (hselect t ht).spec
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    have h := hs.2.2.2.trans
      (selected_card_le_insertedB_width hinv.1 (Finset.card_pos.mp hs.2.1))
    simpa only [tr, selectedTrace, hb, ↓reduceIte, widthCount] using h

theorem SelectedPath.trace_data {M : ℕ} {F G : SAT.CNF (Fin n)} {p : List Bool}
    (hp : SelectedPath M F p G) :
    ∃ (formulas : ℕ → SAT.CNF (Fin n)) (widths : ℕ → ℕ)
      (cores : ℕ → SAT.Clause (Fin n)), formulas 0 = F ∧
      (∀ t < p.length, SparsePriority.Priority (formulas t) M (widths t) (cores t)) ∧
      (∀ t < p.length, formulas (t + 1) = if p.getD t false then
        childB (formulas t) (widths t) (cores t) else
        childA (formulas t) (widths t) (cores t)) := by
  induction hp with
  | nil F =>
    exact ⟨fun _ => F, fun _ => 0, fun _ => ∅, rfl, by simp, by simp⟩
  | @step F G p c H b hs hp ih =>
    obtain ⟨f, w, s, hf, hselect, hnext⟩ := ih
    refine ⟨(fun | 0 => F | t + 1 => f t), (fun | 0 => c | t + 1 => w t),
      (fun | 0 => H | t + 1 => s t), rfl, ?_, ?_⟩
    · intro t ht
      cases t with
      | zero => exact hs
      | succ t => exact hselect t (by simpa using ht)
    · intro t ht
      cases t with
      | zero => simpa using hf
      | succ t => simpa using hnext t (by simpa using ht)

theorem SelectedPath.length_le {M k : ℕ} {F G : SAT.CNF (Fin n)} {p : List Bool}
    (hp : SelectedPath M F p G) (hM : 2 ≤ M)
    (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k F) :
    p.length ≤ depthConstant k M * n := by
  obtain ⟨f, w, s, hf, hs, hn⟩ := hp.trace_data
  apply selected_path_depth_le f w s (fun t => p.getD t false) M k hM hs hn
  · simpa only [hf] using hanti
  · simpa only [hf] using hnt
  · simpa only [hf] using hwidth

theorem SelectedPath.count_true_mul_le {M k : ℕ} {F G : SAT.CNF (Fin n)} {p : List Bool}
    (hp : SelectedPath M F p G) (hM : 2 ≤ M)
    (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k F) :
    p.count true * M ≤ rightConstant k * n := by
  have hpositions : ((Finset.range p.length).filter fun t => p.getD t false = true) =
      BranchTree.bPositions p := by
    ext t
    simp [BranchTree.bPositions, Option.getD_eq_iff]
  obtain ⟨f, w, s, hf, hs, hn⟩ := hp.trace_data
  rw [← BranchTree.card_bPositions_eq_count, ← hpositions]
  apply selected_path_right_steps_mul_le f w s (fun t => p.getD t false) M k hM hs hn
  · simpa only [hf] using hanti
  · simpa only [hf] using hnt
  · simpa only [hf] using hwidth

end SelectedTrace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sharp numerical budgets for disjoint counting sparsification

The frozen counting manuscript, Appendix A, lines 1991–2054. These numerical lemmas do not assert the
existence of a sparsification tree or a primitive implementation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget

open Finset
open scoped BigOperators

open SparseCharging

theorem chooseExponent_spec (k a b : ℕ) (ha : 0 < a) :
    parameterTest k a b (chooseExponent k a b ha) = true :=
  Nat.find_spec (exists_parameter k a b ha)

theorem chooseM_spec (k a b : ℕ) (ha : 0 < a) :
    2 ≤ chooseM k a b ha ∧ rightConstant k ≤ chooseM k a b ha ∧
      rightConstant k * Nat.clog 2 (4 * depthConstant k (chooseM k a b ha) *
        chooseM k a b ha) * b ≤ a * chooseM k a b ha := by
  simpa only [parameterTest, chooseM, decide_eq_true_eq] using chooseExponent_spec k a b ha

/-- The ceiling-log test implies the real exponent budget without a numerical
logarithm oracle. -/
theorem chooseM_log_budget (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (rightConstant k : ℝ) / chooseM k a b ha *
        Real.logb 2 (4 * (depthConstant k (chooseM k a b ha) : ℝ) * chooseM k a b ha) ≤
      (a : ℝ) / b := by
  let M := chooseM k a b ha
  obtain ⟨hM, _, htest⟩ := chooseM_spec k a b ha
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by dsimp [M]; omega)
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hceil : Real.logb 2 (4 * (depthConstant k M : ℝ) * M) ≤
      (Nat.clog 2 (4 * depthConstant k M * M) : ℝ) := by
    have h := Nat.le_ceil (Real.logb (2 : ℕ) (4 * depthConstant k M * M : ℕ))
    rw [Real.natCeil_logb_natCast 2 (4 * depthConstant k M * M)] at h
    simpa using h
  have ht : (rightConstant k : ℝ) * Nat.clog 2 (4 * depthConstant k M * M) * b ≤
      (a : ℝ) * M := by exact_mod_cast htest
  have hmul := mul_le_mul_of_nonneg_left hceil (by positivity : (0 : ℝ) ≤ rightConstant k)
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hMr hbr).mpr
  calc
    (rightConstant k : ℝ) * Real.logb 2 (4 * (depthConstant k M : ℝ) * M) * b ≤
        (rightConstant k : ℝ) * Nat.clog 2 (4 * depthConstant k M * M) * b :=
      mul_le_mul_of_nonneg_right hmul (by positivity)
    _ ≤ (a : ℝ) * M := ht

theorem chooseForSigma_reciprocal (k s : ℕ) (hs : 0 < s)
    (hσ : (0 : ℚ) < 1 / s) :
    chooseForSigma k (1 / s) hσ = chooseM k 1 s (by decide) := by
  have hn : ((1 : ℚ) / s).num = 1 := by
    simpa only [Int.cast_one, Int.cast_natCast] using
      Rat.num_div_eq_of_coprime (a := 1) (b := (s : ℤ))
      (by exact_mod_cast hs) (by simp)
  have hd : ((1 : ℚ) / s).den = s := by
    have hd' : (((1 : ℚ) / s).den : ℤ) = (s : ℤ) := by
      simpa only [Int.cast_one, Int.cast_natCast] using Rat.den_div_eq_of_coprime
        (a := 1) (b := (s : ℤ)) (by exact_mod_cast hs) (by simp)
    exact_mod_cast hd'
  simp only [chooseForSigma, hn, hd, Int.natAbs_one]

theorem chooseForSigma_log_budget (k : ℕ) (σ : ℚ) (hσ : 0 < σ) :
    (rightConstant k : ℝ) / chooseForSigma k σ hσ *
        Real.logb 2 (4 * (depthConstant k (chooseForSigma k σ hσ) : ℝ) *
          chooseForSigma k σ hσ) ≤ (σ : ℝ) := by
  simpa only [chooseForSigma, (rational_data σ hσ).2] using
    chooseM_log_budget k σ.num.natAbs σ.den (rational_data σ hσ).1 σ.pos

/-- The source's explicit node bound for a tree with the charged path budgets.
It applies to an actual finite tree and includes every internal node. -/
theorem nodeCount_le (t : BranchTree.Tree) (C γ n M : ℕ) (σ : ℝ)
    (hC : 1 ≤ C) (hγ : 1 ≤ γ) (hγM : γ ≤ M)
    (hbudget : (γ : ℝ) / M * Real.logb 2 (4 * (C : ℝ) * M) ≤ σ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ C * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ γ * n / M) :
    (t.nodeCount : ℝ) ≤ ((C * n + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  have hpositions : ∀ p ∈ t.paths, (BranchTree.bPositions p).card ≤ γ * n / M := by
    intro p hp
    rw [BranchTree.card_bPositions_eq_count]
    exact hB p hp
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hγpos : (0 : ℝ) < γ := by exact_mod_cast (show 0 < γ by omega)
  have hγone : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hdim : (γ : ℝ) / M ≤ C := by
    have hquot : (γ : ℝ) / M ≤ 1 := (div_le_one hM).mpr (by exact_mod_cast hγM)
    exact hquot.trans (by exact_mod_cast hC)
  by_cases hn : n = 0
  · subst n
    have ht := t.nodeCount_le (C * 0) (γ * 0 / M) hdepth hpositions
    have ht' : t.nodeCount ≤ 1 := by simpa using ht
    simpa using (Nat.cast_le (α := ℝ)).mpr ht'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  let q : ℝ := (γ : ℝ) * n / M
  have hq : 0 < q := by dsimp [q]; positivity
  have hD : q ≤ (C * n : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hdim hnpos.le
    simpa [q, Nat.cast_mul, div_mul_eq_mul_div] using h
  have hR : ((γ * n / M : ℕ) : ℝ) ≤ q := by
    simpa [q, Nat.cast_mul] using (Nat.cast_div_le (m := γ * n) (n := M) (α := ℝ))
  have hbase : 4 * ((C * n : ℕ) : ℝ) / q = 4 * (C : ℝ) * M / γ := by
    dsimp [q]
    push_cast
    field_simp
  have hlog : Real.logb 2 (4 * (C : ℝ) * M / γ) ≤ Real.logb 2 (4 * (C : ℝ) * M) := by
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    exact div_le_self (by positivity) hγone
  have hb : (γ : ℝ) / M * Real.log (4 * (C : ℝ) * M / γ) ≤ Real.log 2 * σ := by
    have hh := (mul_le_mul_of_nonneg_left hlog
      (by positivity : (0 : ℝ) ≤ (γ : ℝ) / M)).trans hbudget
    rw [Real.logb, ← mul_div_assoc, div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))] at hh
    simpa [mul_comm] using hh
  have hbudget' : q * Real.log (4 * ((C * n : ℕ) : ℝ) / q) ≤ Real.log 2 * (σ * n) := by
    rw [hbase]
    have hh := mul_le_mul_of_nonneg_right hb hnpos.le
    convert hh using 1 <;> first | rfl | ((try dsimp [q]) <;> ring)
  have ht := BranchTree.card_paths_le_two_rpow t.paths (C * n) (γ * n / M)
    hq hD hR hdepth hpositions hbudget'
  rw [t.card_paths] at ht
  have hquot : γ * n / M ≤ C * n := by
    calc
      γ * n / M ≤ n := Nat.div_le_of_le_mul (by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hγM)
      _ ≤ C * n := by nlinarith
  have hquotr : ((γ * n / M : ℕ) : ℝ) + 1 ≤ (C * n : ℕ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hquot 1
  refine ht.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _))
  simpa only [Nat.cast_add, Nat.cast_one, pow_two] using
    mul_le_mul_of_nonneg_left hquotr (by positivity : (0 : ℝ) ≤ (C * n : ℕ) + 1)

theorem four_le_depthConstant (k M : ℕ) (hk : 2 ≤ k) : 4 ≤ depthConstant k M := by
  have hsum : 1 ≤ ∑ j ∈ range (k - 1), (3 * M) ^ j := by
    simpa using (Finset.single_le_sum (f := fun j => (3 * M) ^ j)
      (fun _ _ => Nat.zero_le _) (show 0 ∈ range (k - 1) from mem_range.mpr (by omega)))
  exact Nat.mul_le_mul_left 4 hsum

theorem four_le_rightConstant (k : ℕ) (hk : 2 ≤ k) : 4 ≤ rightConstant k := by
  simpa [depthConstant, rightConstant] using four_le_depthConstant k 1 hk

theorem selected_nodeCount_le (t : BranchTree.Tree) (k n : ℕ) (σ : ℚ)
    (hk : 2 ≤ k) (hσ : 0 < σ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ depthConstant k (chooseForSigma k σ hσ) * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ rightConstant k * n / chooseForSigma k σ hσ) :
    (t.nodeCount : ℝ) ≤
      ((depthConstant k (chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) := by
  have hspec := chooseM_spec k σ.num.natAbs σ.den (rational_data σ hσ).1
  exact nodeCount_le t (depthConstant k (chooseForSigma k σ hσ)) (rightConstant k)
    n (chooseForSigma k σ hσ) σ
    (by have := four_le_depthConstant k (chooseForSigma k σ hσ) hk; omega)
    (by have := four_le_rightConstant k hk; omega) hspec.2.1
    (chooseForSigma_log_budget k σ hσ) hdepth hB

/-- Discharge the numeric path premises from actual priority-selected paths. -/
theorem selectedPaths_nodeCount_le {n : ℕ} (t : BranchTree.Tree)
    (F : SAT.CNF (Fin n)) (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ)
    (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k F)
    (hpaths : ∀ p ∈ t.paths, ∃ G, SelectedPath (chooseForSigma k σ hσ) F p G) :
    (t.nodeCount : ℝ) ≤
      ((depthConstant k (chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) := by
  have hM : 2 ≤ chooseForSigma k σ hσ :=
    (chooseM_spec k σ.num.natAbs σ.den (rational_data σ hσ).1).1
  apply selected_nodeCount_le t k n σ hk hσ
  · intro p hp
    obtain ⟨G, hG⟩ := hpaths p hp
    exact hG.length_le hM hanti hnt hwidth
  · intro p hp
    obtain ⟨G, hG⟩ := hpaths p hp
    exact (Nat.le_div_iff_mul_le (by omega)).mpr
      (hG.count_true_mul_le hM hanti hnt hwidth)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: the mathematical depth-first transition and its count invariant.

The transition below specifies a leaf operation by its exact count. It is not a
primitive implementation of that operation, and no bit-time bound is asserted.
The pending list retains the current node and one sibling per branch on the
active path; completed leaves are discarded immediately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

open SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

theorem PriorityDerivation.selectedPaths {M : ℕ} {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (h : PriorityDerivation M F tree) :
    ∀ p ∈ tree.paths, ∃ G, SparseCharging.SelectedPath M F p G := by
  induction h with
  | @leaf F ht =>
    intro p hp
    simp only [BranchTree.Tree.paths, Finset.mem_singleton] at hp
    subst p
    exact ⟨F, .nil F⟩
  | @branch F c H A B hp hA hB ihA ihB =>
    intro p hmem
    simp only [BranchTree.Tree.paths, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hmem
    rcases hmem with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨F, .nil F⟩
    · obtain ⟨G, hG⟩ := ihA q hq
      exact ⟨G, .step false hp hG⟩
    · obtain ⟨G, hG⟩ := ihB q hq
      exact ⟨G, .step true hp hG⟩

theorem PriorityDerivation.nodeCount_bound {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ)
    (h : PriorityDerivation (SparseBudget.chooseForSigma k σ hσ) F tree)
    (hanti : SunflowerBranch.Antichain F) (hnt : ∀ C ∈ F, ¬ C.IsTautology)
    (hwidth : WidthAtMost k F) :
    (tree.nodeCount : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) :=
  SparseBudget.selectedPaths_nodeCount_le tree F k σ hk hσ hanti hnt hwidth h.selectedPaths


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

theorem selectedRaw_set {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (c : ℕ) (H : List (SAT.Literal V))
    (hF : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (selectedRaw F c H) =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  ext D
  simp only [ExecCNF.mem_formulaSet, DisjointBranch.mem_selected]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨hCF, htest⟩ := List.mem_filter.mp hC
    obtain ⟨hc, hsub⟩ := Bool.and_eq_true_iff.mp htest
    have hcard := List.toFinset_card_of_nodup (hF C hCF)
    exact ⟨⟨C, hCF, rfl⟩, hcard.trans (of_decide_eq_true hc),
      (ExecCNF.subset_true H C).mp hsub⟩
  · rintro ⟨⟨C, hCF, rfl⟩, hc, hsub⟩
    refine ⟨C, List.mem_filter.mpr ⟨hCF, ?_⟩, rfl⟩
    apply Bool.and_eq_true_iff.mpr
    have hcard := List.toFinset_card_of_nodup (hF C hCF)
    exact ⟨decide_eq_true (hcard.symm.trans hc), (ExecCNF.subset_true H C).mpr hsub⟩

theorem selectedRaw_length {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (c : ℕ) (H : List (SAT.Literal V))
    (hF : ∀ C ∈ F, C.Nodup) (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    (selectedRaw F c H).length =
      SparsePriority.degree (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  have hn : ((selectedRaw F c H).map ExecCNF.clauseSet).Nodup :=
    (List.Sublist.map ExecCNF.clauseSet List.filter_sublist).nodup hdistinct
  have hc := List.toFinset_card_of_nodup hn
  change (ExecCNF.formulaSet (selectedRaw F c H)).card = _ at hc
  rw [selectedRaw_set F c H hF, List.length_map] at hc
  exact hc.symm

theorem masked_sublist {α : Type*} (mask : List Bool) (C : List α) :
    (masked mask C).Sublist C := by
  induction C generalizing mask with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [masked]
    split
    · exact .cons_cons x (ih mask.tail)
    · exact .cons x (ih mask.tail)

theorem masked_membership {α : Type*} [DecidableEq α] (C : List α) (H : Finset α)
    (suffix : List Bool) :
    masked (C.map (fun x => decide (x ∈ H)) ++ suffix) C = C.filter (fun x => decide (x ∈ H)) := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ H <;> simp [masked, hx, ih]

theorem exists_masked {α : Type*} [DecidableEq α] (k : ℕ) (C : List α) (H : Finset α)
    (hC : C.length ≤ k) (hH : H ⊆ C.toFinset) :
    ∃ mask ∈ masks k, (masked mask C).toFinset = H := by
  let mask := C.map (fun x => decide (x ∈ H)) ++ List.replicate (k - C.length) false
  refine ⟨mask, (mem_masks mask k).mpr ?_, ?_⟩
  · simp [mask, Nat.add_sub_of_le hC]
  · rw [show masked mask C = C.filter (fun x => decide (x ∈ H)) from masked_membership C H _]
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨by simpa using hH h, h⟩⟩

theorem rawCandidates_complete {α : Type*} [DecidableEq α]
    (k : ℕ) (F : List (List α)) (C : List α) (H : Finset α)
    (hC : C ∈ F) (hwidth : C.length ≤ k) (hH : H ⊆ C.toFinset) :
    ∃ core, (C.length, core) ∈ rawCandidates k F ∧ core.toFinset = H ∧ core.Sublist C := by
  obtain ⟨mask, hm, he⟩ := exists_masked k C H hwidth hH
  refine ⟨masked mask C, ?_, he, masked_sublist mask C⟩
  exact List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨mask, hm, rfl⟩⟩

theorem rawCandidate_spec {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, C.length = c ∧ H.Sublist C := by
  obtain ⟨C, hC, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, _, hp⟩ := List.mem_map.mp hm
  obtain ⟨hc, hH⟩ := Prod.mk.inj hp
  exact ⟨C, hC, hc, hH ▸ masked_sublist mask C⟩

theorem represent_core {n : ℕ} (k : ℕ) (F : List (List (SAT.Literal (Fin n))))
    (c : ℕ) (H : SAT.Clause (Fin n))
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdegree : 0 < SparsePriority.degree (ExecCNF.formulaSet F) c H) :
    ∃ core, (c, core) ∈ rawCandidates k F ∧ ExecCNF.clauseSet core = H ∧ core.length = H.card := by
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hdegree
  obtain ⟨hCF, hc, hH⟩ := DisjointBranch.mem_selected.mp hC
  obtain ⟨rawC, hrawC, rfl⟩ := ExecCNF.mem_formulaSet.mp hCF
  have hrawlen : rawC.length = c :=
    (List.toFinset_card_of_nodup (hnodup rawC hrawC)).symm.trans hc
  obtain ⟨core, hcore, he, hsub⟩ :=
    rawCandidates_complete k F rawC H hrawC (hwidth rawC hrawC) hH
  have hnodupCore := hsub.nodup (hnodup rawC hrawC)
  refine ⟨core, hrawlen ▸ hcore, he, ?_⟩
  exact (List.toFinset_card_of_nodup hnodupCore).symm.trans (congrArg Finset.card he)

theorem RawPriority.toPriority {n : ℕ} {k : ℕ} {F : List (List (SAT.Literal (Fin n)))}
    {M c : ℕ} {H : List (SAT.Literal (Fin n))} (h : RawPriority k F M c H) (hM : 0 < M)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    SparsePriority.Priority (ExecCNF.formulaSet F) M c (ExecCNF.clauseSet H) := by
  obtain ⟨C, hCF, hc, hsub⟩ := rawCandidate_spec k F c H h.candidate
  have hHnodup := hsub.nodup (hnodup C hCF)
  have hHcard : (ExecCNF.clauseSet H).card = H.length := List.toFinset_card_of_nodup hHnodup
  have hCcard : (ExecCNF.clauseSet C).card = c :=
    (List.toFinset_card_of_nodup (hnodup C hCF)).trans hc
  refine ⟨⟨ExecCNF.clauseSet C, ExecCNF.mem_formulaSet.mpr ⟨C, hCF, rfl⟩, hCcard, ?_⟩,
    hHcard.symm ▸ h.core_nonempty, hHcard.symm ▸ h.core_proper, ?_, ?_, ?_⟩
  · intro l hl
    exact ExecCNF.mem_clauseSet.mpr (hsub.subset (ExecCNF.mem_clauseSet.mp hl))
  · simpa only [hHcard, selectedRaw_length F c H hnodup hdistinct] using h.threshold
  · intro d S hS hSd hdc
    by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) d S = 0
    · rw [hz]; exact pow_pos hM _
    obtain ⟨core, hcore, he, hlen⟩ := represent_core k F d S hwidth hnodup (Nat.pos_of_ne_zero hz)
    have hf := h.minimum d core hcore (by omega) (by omega) hdc
    simpa only [selectedRaw_length F d core hnodup hdistinct, he, hlen] using hf
  · intro S hHS hSc
    by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) c S = 0
    · rw [hz]; exact pow_pos hM _
    obtain ⟨core, hcore, he, hlen⟩ := represent_core k F c S hwidth hnodup (Nat.pos_of_ne_zero hz)
    have hf := h.maximum core hcore (by omega) (by omega)
    simpa only [selectedRaw_length F c core hnodup hdistinct, he, hlen] using hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

theorem negatedUnits_set {V : Type*} [DecidableEq V] (H : List (Literal V)) :
    ExecCNF.formulaSet (negatedUnits Literal.negate H) =
      DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) := by
  ext C
  simp [negatedUnits, ExecCNF.formulaSet, ExecCNF.clauseSet,
    DisjointBranch.negatedCoreUnits, Finset.mem_image]

theorem resultA_set {V : Type*} [DecidableEq V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    ExecCNF.formulaSet (ExecCoreChildProgram.result F S H) =
      DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  simpa only [hS, DisjointBranch.childA, SAT.absorb] using
    ExecCoreChildProgram.result_set F S H

theorem units_disjoint_selected {V : Type*} [DecidableEq V]
    (F : CNF V) (c : ℕ) (H : Clause V) (hc : 2 ≤ c) :
    Disjoint (DisjointBranch.negatedCoreUnits H) (DisjointBranch.selected F c H) := by
  apply Finset.disjoint_left.mpr
  intro U hU hsel
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hU
  have hcard := (DisjointBranch.mem_selected.mp hsel).2.1
  rw [Finset.card_singleton] at hcard
  omega

theorem resultB_set {V : Type*} [DecidableEq V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ) (hc : 2 ≤ c)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    ExecCNF.formulaSet (resultB Literal.negate F S H) =
      DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  have hdisj := units_disjoint_selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) hc
  have hdiff :
      (DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) ∪ ExecCNF.formulaSet F) \
        DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) =
      DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) ∪
        (ExecCNF.formulaSet F \
          DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) := by
    rw [Finset.union_sdiff_distrib, hdisj.sdiff_eq_left]
  unfold resultB
  rw [ExecPetalChildProgram.result_set]
  change SAT.absorb (_ ∪ (_ \ _)) = _
  rw [ExecCNF.formulaSet_append, negatedUnits_set, hS, hdiff]
  unfold DisjointBranch.childB DisjointBranch.petals SunflowerBranch.petalFamily
  apply congrArg SAT.absorb
  ac_rfl

open BitProgram StructuredCalls

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CountDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed refinement of the concrete streaming frontier.

Depths and derivation trees below are proof indices. The physical pending tape
contains only formula bodies, and every formula keeps the same declared `Fin n`.
The selector and leaf execution contracts must still be supplied by their actual
finite programs; this module does not postulate a final counting service.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}

theorem childA_set (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n)))
    (hnodup : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (childA F c H) =
      DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) :=
  DisjointBranchProgram.resultA_set F (selectedRaw F c H) H c
    (selectedRaw_set F c H hnodup)

theorem childB_set (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n)))
    (hc : 2 ≤ c) (hnodup : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (childB F c H) =
      DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) :=
  DisjointBranchProgram.resultB_set F (selectedRaw F c H) H c hc
    (selectedRaw_set F c H hnodup)

theorem Derivation.toPriority {k M : ℕ} {F : RawCNF n} {tree : BranchTree.Tree}
    (h : Derivation k M F tree) (hM : 0 < M) :
    SparseCountProgram.PriorityDerivation M (ExecCNF.formulaSet F) tree := by
  induction h with
  | leaf hnone => exact .leaf hnone
  | @branch F c H A B hv hp _ _ ihA ihB =>
      have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
      rw [childA_set F c H hv.literal_nodup] at ihA
      rw [childB_set F c H hc hv.literal_nodup] at ihB
      exact .branch (hp.toPriority hM hv.width hv.literal_nodup hv.clause_nodup) ihA ihB


theorem Derivation.nodeCount_bound {F : RawCNF n} {tree : BranchTree.Tree}
    (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ)
    (h : Derivation k (SparseBudget.chooseForSigma k σ hσ) F tree) (hv : Valid k F) :
    (tree.nodeCount : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) := by
  have hM : 2 ≤ SparseBudget.chooseForSigma k σ hσ :=
    (SparseBudget.chooseM_spec k σ.num.natAbs σ.den
      (SparseBudget.rational_data σ hσ).1).1
  exact (h.toPriority (by omega)).nodeCount_bound k σ hk hσ
    hv.antichain hv.not_tautological (formulaSet_width_le F hv.width)


open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCompletedTree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A completed concrete transition history determines a proof-only branch
forest backwards. This transfers the sharp tree-node bound to the actual
number of visits, without storing a tree or list of visits on the machine.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree

open SparseDFSRefinement
variable {n : ℕ}

theorem transition_backward {k M : ℕ} {s t : Frontier n} {trees : List BranchTree.Tree}
    (h : Transition k M s t) (hf : Forest k M t.pending trees) :
    ∃ earlier, Forest k M s.pending earlier ∧ nodes earlier = nodes trees + 1 := by
  cases h with
  | leaf node rest total hnone =>
    refine ⟨.leaf :: trees, .cons (.leaf hnone) hf, ?_⟩
    simp [nodes, BranchTree.Tree.nodeCount, Nat.add_comm]
  | branch node rest total c H hv hp =>
    cases hf with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        refine ⟨_ :: _, .cons (.branch hv hp left right) tail, ?_⟩
        simp only [nodes, List.map_cons, List.sum_cons, BranchTree.Tree.nodeCount]
        omega

theorem transitions_backward {k M visits : ℕ} {s t : Frontier n}
    (h : Transitions k M visits s t) {trees : List BranchTree.Tree}
    (hf : Forest k M t.pending trees) :
    ∃ earlier, Forest k M s.pending earlier ∧ nodes earlier = visits + nodes trees := by
  induction h generalizing trees with
  | refl => exact ⟨trees, hf, by omega⟩
  | cons first _ ih =>
    obtain ⟨middle, hm, hsum⟩ := ih hf
    obtain ⟨earlier, he, hnodes⟩ := transition_backward first hm
    exact ⟨earlier, he, by omega⟩

/-- Exact visit count, independent of the physical selector's tie breaking. -/
theorem completed_tree {k M visits total : ℕ} {F : RawCNF n}
    (h : Transitions k M visits ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    ∃ tree, Derivation k M F tree ∧ tree.nodeCount = visits := by
  obtain ⟨trees, ht, hnodes⟩ := transitions_backward h Forest.nil
  cases ht with
  | cons root tail =>
    cases tail
    exact ⟨_, root, by simpa [nodes] using hnodes⟩

theorem completed_visits_bound {F : RawCNF n} {visits total : ℕ}
    (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ) (hv : Valid k F)
    (h : Transitions k (SparseBudget.chooseForSigma k σ hσ) visits
      ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    (visits : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) := by
  obtain ⟨tree, ht, hcount⟩ := completed_tree h
  rw [← hcount]
  exact ht.nodeCount_bound k σ hk hσ hv

/-- The parameter program produces the threshold for the reciprocal budget.
This form matches its natural-number output without rational representation
assumptions at the native interface. -/
theorem completed_visits_reciprocal_oai {F : RawCNF n} {visits total : ℕ}
    (k s : ℕ) (hk : 2 ≤ k) (hs : 0 < s) (hv : Valid k F)
    (h : Transitions k (SparseBudget.chooseM k 1 s (by decide)) visits
      ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    (visits : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseM k 1 s (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((n : ℝ) / s) := by
  have hσ : (0 : ℚ) < 1 / s := div_pos (by norm_num) (by exact_mod_cast hs)
  have hthreshold := SparseBudget.chooseForSigma_reciprocal k s hs hσ
  have bound := completed_visits_bound k (1 / s) hk hσ hv (hthreshold.symm ▸ h)
  simpa only [hthreshold, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    one_div_mul_eq_div] using bound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal_oai
