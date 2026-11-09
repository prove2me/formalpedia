-- Prove2me | solution 1 for OAI.MUB6.fourier_and_family_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:17:53.6332+00:00
-- url     : https://prove2.me/submissions/1ca08baf-712d-4504-856e-87fc5066d728
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E139
import Definitions.Def_OAIQ106E149
import Definitions.Def_OAIQ106E154
import Definitions.Def_OAIQ106E167
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_allRowsSound_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_expandedIdentity1_e
import Theorems.Thm_OAI_MUB6_family_size_le_five_e
import Theorems.Thm_OAI_MUB6_pair_cross_certificate_e

section
-- module Solutions.OAIQ106_MUB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_perm {a b : Sparse ι} (h : a.Perm b) (x : ι → ℝ) :
    eval a x = eval b x := by
  unfold eval
  exact (h.map fun p : ι × ℤ => (p.2 : ℝ) * x p.1).sum_eq

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three-by-three block obstruction in cubic classification, proved by
Newton's determinant identity instead of a dimension argument. -/

noncomputable section
open scoped BigOperators ComplexConjugate Matrix

namespace MUB6

theorem trace_newton_three (C : Matrix (Fin 3) (Fin 3) ℂ) :
    6 * C.det = C.trace ^ 3 - 3 * C.trace * (C * C).trace +
      2 * (C * C * C).trace := by
  simp [Matrix.det_fin_three, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- A three-dimensional projection cannot have rank three halves.  This
formulation needs only polynomial identities over the complex numbers. -/
theorem no_three_by_three_scaled_projection (C : Matrix (Fin 3) (Fin 3) ℂ)
    (hC : C * C = (6 : ℂ) • C) (ht : C.trace = 9) : False := by
  have ht2 : (C * C).trace = 54 := by rw [hC, Matrix.trace_smul, ht]; norm_num
  have ht3 : (C * C * C).trace = 324 := by
    rw [hC, Matrix.smul_mul, hC, Matrix.trace_smul, Matrix.trace_smul, ht]
    norm_num
  have hn := trace_newton_three C
  rw [ht, ht2, ht3] at hn
  have hd : C.det = (-27 / 2 : ℂ) := by linear_combination hn / 6
  have hdm := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_smul, hd] at hdm
  norm_num at hdm

/-- The two classes of three restricted rows cannot be mutually orthogonal
when their combined columns are orthogonal and every entry has modulus one. -/
theorem no_cubic_three_by_three_block
    (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (hunit : ∀ i j, Complex.normSq (A i j) = 1)
    (hcross : A * B.conjTranspose = 0)
    (hcol : A.conjTranspose * A + B.conjTranspose * B = (6 : ℂ) • 1) : False := by
  let C := A.conjTranspose * A
  have hCD : C * (B.conjTranspose * B) = 0 := by
    dsimp [C]
    calc
      A.conjTranspose * A * (B.conjTranspose * B) =
          A.conjTranspose * (A * B.conjTranspose) * B := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hcross, Matrix.mul_zero, Matrix.zero_mul]
  have hC : C * C = (6 : ℂ) • C := by
    calc
      C * C = C * (C + B.conjTranspose * B) := by rw [Matrix.mul_add, hCD, add_zero]
      _ = C * ((6 : ℂ) • 1) := by rw [hcol]
      _ = (6 : ℂ) • C := by rw [Matrix.mul_smul, Matrix.mul_one]
  have ht : C.trace = 9 := by
    have hh (i j : Fin 3) : conj (A i j) * A i j = (1 : ℂ) := by
      rw [mul_comm, Complex.mul_conj, hunit]
      rfl
    change (∑ i, ∑ j, conj (A j i) * A j i) = 9
    norm_num [hh]
  exact no_three_by_three_scaled_projection C hC ht

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-support step of the cubic classification in §3.

These lemmas concern two three-element supports avoiding coordinate zero.
The last theorem states that a quotient having the cubed-value pattern proved
for Hadamard row ratios forces the supports to coincide.
-/

noncomputable section

namespace MUB6

theorem value_pair_exhausts (f : (Fin 6) → ℂ)
    (hf : ∃ a b : ℂ, ∀ i, f i = a ∨ f i = b)
    (i j : (Fin 6)) (hij : f i ≠ f j) : ∀ k, f k = f i ∨ f k = f j := by
  obtain ⟨a, b, hf⟩ := hf
  rcases hf i with hi | hi
  · rcases hf j with hj | hj
    · exact False.elim (hij (hi.trans hj.symm))
    · intro k
      exact (hf k).imp (fun h => h.trans hi.symm) (fun h => h.trans hj.symm)
  · rcases hf j with hj | hj
    · intro k
      exact (hf k).symm.imp (fun h => h.trans hi.symm) (fun h => h.trans hj.symm)
    · exact False.elim (hij (hi.trans hj.symm))

theorem three_supports_have_witnesses (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3)
    (hS0 : (0 : (Fin 6)) ∉ S) (hU0 : (0 : (Fin 6)) ∉ U) (hne : S ≠ U) :
    (S \ U).Nonempty ∧ (U \ S).Nonempty ∧ (S ∩ U).Nonempty := by
  have hSU : (S \ U).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hne
    exact Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.mp h) (by omega)
  have hUS : (U \ S).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hne
    exact (Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.mp h) (by omega)).symm
  have hbound : (S ∪ U).card ≤ 5 := by
    have hsub : S ∪ U ⊆ (Finset.univ : Finset (Fin 6)).erase 0 := by
      intro i hi
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
      intro heq
      subst i
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hS0 hi
      · exact hU0 hi
    simpa using Finset.card_le_card hsub
  have hcount : (S ∪ U).card + (S ∩ U).card = 6 := by
    simpa [hS, hU] using Finset.card_union_add_card_inter S U
  have hpos : 0 < (S ∩ U).card := by omega
  exact ⟨hSU, hUS, Finset.card_pos.mp hpos⟩

/-- For two subsets of size three in a six-element set, the number of
coordinates on which membership agrees is even, hence cannot be three. -/
theorem same_membership_card_ne_three (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3) :
    (Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U))).card ≠ 3 := by
  have heq : Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U)) =
      (S ∩ U) ∪ (S ∪ U)ᶜ := by
    ext i
    by_cases hs : i ∈ S <;> by_cases hu : i ∈ U <;> simp [hs, hu]
  have hdisj : Disjoint (S ∩ U) (S ∪ U)ᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hi hnot
    exact (Finset.mem_compl.mp hnot)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hi).1))
  have hcount : (S ∪ U).card + (S ∩ U).card = 6 := by
    simpa [hS, hU] using Finset.card_union_add_card_inter S U
  intro hbad
  rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_compl] at hbad
  change (S ∩ U).card + (6 - (S ∪ U).card) = 3 at hbad
  omega

/-- The exact common-support claim: a ratio of two nonconstant cubed rows
cannot have the necessary three-and-three multiplicities on distinct supports. -/
theorem common_support_of_twoValuePattern (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3)
    (hS0 : (0 : (Fin 6)) ∉ S) (hU0 : (0 : (Fin 6)) ∉ U)
    (x y : ℂ) (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hp : TwoValuePattern (supportedRatio S U x y)) : S = U := by
  classical
  by_contra hne
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩, ⟨u, hu⟩⟩ :=
    three_supports_have_witnesses S U hS hU hS0 hU0 hne
  obtain ⟨hsS, hsU⟩ := Finset.mem_sdiff.mp hs
  obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
  obtain ⟨huS, huU⟩ := Finset.mem_inter.mp hu
  let f := supportedRatio S U x y
  have hf0 : f 0 = 1 := by simp [f, supportedRatio, supportedValue, hS0, hU0]
  have hfs : f s = x := by simp [f, supportedRatio, supportedValue, hsS, hsU]
  have hft : f t = y⁻¹ := by simp [f, supportedRatio, supportedValue, htS, htU]
  have hfu : f u = x / y := by simp [f, supportedRatio, supportedValue, huS, huU]
  have hdist : f 0 ≠ f s := by simpa [hf0, hfs] using Ne.symm hx1
  have hvalues : ∀ i, f i = 1 ∨ f i = x := by
    simpa [hf0, hfs] using value_pair_exhausts f hp.1 0 s hdist
  have hinv : y⁻¹ = x := by
    have htvalues := hvalues t
    rw [hft] at htvalues
    exact htvalues.resolve_left (by simpa using hy1)
  have hxx : x ^ 2 = 1 ∨ x ^ 2 = x := by
    have huvalues := hvalues u
    simpa [hfu, div_eq_mul_inv, hinv, pow_two] using huvalues
  have hsq : x ^ 2 = 1 := by
    rcases hxx with h | h
    · exact h
    · have hprod : x * (x - 1) = 0 := by linear_combination h
      exact False.elim (hx1 (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hx0)))
  have hxminus : x = -1 := (sq_eq_one_iff.mp hsq).resolve_left hx1
  have hyminus : y = -1 := by
    have h := congrArg (fun z : ℂ => z⁻¹) hinv
    simpa [hxminus] using h
  have hones : (Finset.univ.filter (fun i => f i = 1)).card = 3 :=
    hp.2 1 ⟨0, hf0⟩ ⟨s, by change f s ≠ 1; rw [hfs]; exact hx1⟩
  have hset : Finset.univ.filter (fun i => f i = 1) =
      Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U)) := by
    ext i
    by_cases hs : i ∈ S <;> by_cases hu : i ∈ U <;>
      norm_num [f, supportedRatio, supportedValue, hxminus, hyminus, hs, hu]
  rw [hset] at hones
  exact same_membership_card_ne_three S U hS hU hones

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From cubed row-ratio patterns to the single three-by-three exceptional block. -/

noncomputable section

namespace MUB6

theorem twoValuePattern_supported (f : Fin 6 → ℂ) (hf : TwoValuePattern f)
    (hf0 : f 0 = 1) (j : Fin 6) (hj : f j ≠ 1) :
    (nonOneSupport f).card = 3 ∧ (0 : Fin 6) ∉ nonOneSupport f ∧
      ∀ i, f i = supportedValue (nonOneSupport f) (f j) i := by
  classical
  have hd : f 0 ≠ f j := by rw [hf0]; exact Ne.symm hj
  have hv : ∀ i, f i = 1 ∨ f i = f j := by
    simpa only [hf0] using value_pair_exhausts f hf.1 0 j hd
  have hs : nonOneSupport f = Finset.univ.filter (fun i => f i = f j) := by
    ext i
    simp only [mem_nonOneSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => (hv i).resolve_left h
    · intro h
      simpa only [h] using hj
  refine ⟨?_, by simp [hf0], ?_⟩
  · rw [hs]
    exact hf.2 (f j) ⟨j, rfl⟩ ⟨0, hd⟩
  · intro i
    by_cases hi : f i = 1
    · simp [supportedValue, hi]
    · simp [supportedValue, (hv i).resolve_left hi]

theorem dephased_pattern_single_block (F : Fin 6 → Fin 6 → ℂ)
    (h0row : ∀ j, F 0 j = 1) (h0col : ∀ i, F i 0 = 1)
    (hnz : ∀ i j, F i j ≠ 0)
    (hrow : ∀ i, TwoValuePattern (F i))
    (hcol : ∀ j, TwoValuePattern (fun i => F i j))
    (hratio : ∀ i r, i ≠ r → TwoValuePattern (fun j => F i j / F r j))
    (i j : Fin 6) (hij : F i j ≠ 1) :
    ∃ (R S : Finset (Fin 6)) (x : ℂ),
      R.card = 3 ∧ S.card = 3 ∧ (0 : Fin 6) ∉ R ∧ (0 : Fin 6) ∉ S ∧
      x ≠ 0 ∧ x ≠ 1 ∧
      ∀ r c, F r c = if r ∈ R ∧ c ∈ S then x else 1 := by
  classical
  let R := nonOneSupport (fun r => F r j)
  let S := nonOneSupport (F i)
  obtain ⟨hScard, hS0, hSvalue⟩ :=
    twoValuePattern_supported (F i) (hrow i) (h0col i) j hij
  obtain ⟨hRcard, hR0, hRvalue⟩ :=
    twoValuePattern_supported (fun r => F r j) (hcol j) (h0row j) i hij
  have hsamesupport (r c : Fin 6) (hrc : F r c ≠ 1) : nonOneSupport (F r) = S := by
    by_cases hri : r = i
    · subst r
      rfl
    obtain ⟨hUcard, hU0, hUvalue⟩ :=
      twoValuePattern_supported (F r) (hrow r) (h0col r) c hrc
    apply common_support_of_twoValuePattern _ _ hUcard hScard hU0 hS0
      (F r c) (F i j) (hnz r c) hrc hij
    have hq := hratio r i hri
    have heq : (fun k => F r k / F i k) =
        supportedRatio (nonOneSupport (F r)) S (F r c) (F i j) := by
      funext k
      rw [hUvalue k, hSvalue k]
      rfl
    rwa [← heq]
  refine ⟨R, S, F i j, hRcard, hScard, hR0, hS0, hnz i j, hij, ?_⟩
  intro r c
  by_cases hr : r ∈ R
  · have hr' : r ∈ nonOneSupport (fun r => F r j) := hr
    have hrj : F r j ≠ 1 := (mem_nonOneSupport (fun r => F r j) r).mp hr'
    obtain ⟨_, _, hv⟩ :=
      twoValuePattern_supported (F r) (hrow r) (h0col r) j hrj
    have hval : F r j = F i j := by
      simpa only [supportedValue, ite_eq_left hr'] using hRvalue r
    rw [hv c, hsamesupport r j hrj, hval]
    simp [supportedValue, hr]
  · have hrc : F r c = 1 := by
      by_contra hc
      have hs := hsamesupport r c hc
      have hjS : j ∈ S := (mem_nonOneSupport _ _).mpr hij
      have hjU : j ∈ nonOneSupport (F r) := by rwa [hs]
      exact hr ((mem_nonOneSupport (fun r => F r j) r).mpr
        ((mem_nonOneSupport (F r) j).mp hjU))
    simp [hr, hrc]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary symmetric sums for the six-entry cubic classification. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_product_complement (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1) (s : Finset (Fin 6)) :
    (∏ i, v i) * conj (∏ i ∈ s, v i) = ∏ i ∈ sᶜ, v i := by
  rw [← Finset.prod_mul_prod_compl s v, map_prod]
  calc
    ((∏ i ∈ s, v i) * ∏ i ∈ sᶜ, v i) * ∏ i ∈ s, conj (v i) =
        (∏ i ∈ sᶜ, v i) * ∏ i ∈ s, (v i * conj (v i)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∏ i ∈ sᶜ, v i := by simp [Complex.mul_conj, hv]

theorem elementarySum_reciprocal (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1) (k : ℕ) (hk : k ≤ 6) :
    (∏ i, v i) * conj (elementarySum v k) = elementarySum v (6 - k) := by
  unfold elementarySum
  rw [map_sum, Finset.mul_sum]
  simp_rw [unit_product_complement v hv]
  refine Finset.sum_bij (fun s _ => sᶜ) ?_ ?_ ?_ ?_
  · intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    simp [Finset.mem_powersetCard, Finset.card_compl, hc]
  · intro s _hs t _ht h
    simpa using congrArg (fun u : Finset (Fin 6) => uᶜ) h
  · intro t ht
    refine ⟨tᶜ, ?_, by simp⟩
    have hc := (Finset.mem_powersetCard.mp ht).2
    have hsub : 6 - (6 - k) = k := by omega
    simp [Finset.mem_powersetCard, Finset.card_compl, hc, hsub]
  · intro _subset _membership
    rfl

theorem elementarySum_zero (v : (Fin 6) → ℂ) : elementarySum v 0 = 1 := by
  simp [elementarySum]

theorem elementarySum_six (v : (Fin 6) → ℂ) : elementarySum v 6 = ∏ i, v i := by
  have h : (Finset.univ : Finset (Fin 6)).powersetCard 6 = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 6))
  simp [elementarySum, h]

theorem elementarySum_one (v : (Fin 6) → ℂ) : elementarySum v 1 = ∑ i, v i := by
  simp [elementarySum, Finset.powersetCard_one]

private theorem coordinate_pairs :
    (Finset.univ : Finset (Fin 6)).powersetCard 2 =
      {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5},
       {1, 2}, {1, 3}, {1, 4}, {1, 5},
       {2, 3}, {2, 4}, {2, 5}, {3, 4}, {3, 5}, {4, 5}} := by
  decide

/-- Newton's identity at degree two, specialized to exactly six entries. -/
theorem elementarySum_two_identity (v : (Fin 6) → ℂ) :
    (∑ i, v i) ^ 2 = (∑ i, v i ^ 2) + 2 * elementarySum v 2 := by
  simp (disch := decide) [elementarySum, coordinate_pairs, Fin.sum_univ_succ]
  ring

theorem elementarySum_one_two_zero (v : (Fin 6) → ℂ)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    elementarySum v 1 = 0 ∧ elementarySum v 2 = 0 := by
  refine ⟨by simpa [elementarySum_one] using h1, ?_⟩
  have h := elementarySum_two_identity v
  rw [h1, h2] at h
  linear_combination -h / 2

theorem elementarySum_four_five_zero (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    elementarySum v 4 = 0 ∧ elementarySum v 5 = 0 := by
  obtain ⟨h1', h2'⟩ := elementarySum_one_two_zero v h1 h2
  constructor
  · simpa [h2'] using (elementarySum_reciprocal v hv 2 (by decide)).symm
  · simpa [h1'] using (elementarySum_reciprocal v hv 1 (by decide)).symm

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicMultiplicityCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicity counting once the two possible cubed values are known. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_cube_mul_conj_square {z : ℂ} (hz : Complex.normSq z = 1) :
    z ^ 3 * (conj z) ^ 2 = z := by
  calc
    z ^ 3 * (conj z) ^ 2 = z * (z * conj z) ^ 2 := by ring
    _ = z := by simp [Complex.mul_conj, hz]

/-- A nonempty zero-sum collection of nonzero numbers with the same cube has
at least three members: one term cannot vanish, and two opposite terms have
opposite cubes. -/
theorem same_cube_zero_sum_card_ge_three (v : (Fin 6) → ℂ) (s : Finset (Fin 6))
    (a : ℂ) (ha : a ≠ 0) (hne : s.Nonempty)
    (hcube : ∀ i ∈ s, v i ^ 3 = a) (hsum : ∑ i ∈ s, v i = 0) :
    3 ≤ s.card := by
  by_contra h
  have hp := hne.card_pos
  have hc : s.card = 1 ∨ s.card = 2 := by omega
  rcases hc with hc | hc
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    have hi := hcube i (by simp)
    simp only [Finset.sum_singleton] at hsum
    exact ha (by simpa [hsum] using hi.symm)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hc
    have hi := hcube i (by simp)
    have hj := hcube j (by simp)
    have hsum' : v i + v j = 0 := by simpa [hij] using hsum
    have hneg : v i = -v j := eq_neg_of_add_eq_zero_left hsum'
    have hanti : -a = a := by
      calc
        -a = -(v j ^ 3) := by rw [hj]
        _ = (-v j) ^ 3 := by ring
        _ = a := by simpa only [hneg] using hi
    apply ha
    linear_combination -(1 / 2 : ℂ) * hanti

theorem two_cube_classes_card_three (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0)
    (a b : ℂ) (hab : a ≠ b)
    (hvalues : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b)
    (ia ib : (Fin 6)) (hia : v ia ^ 3 = a) (hib : v ib ^ 3 = b) :
    (cubeClass v a).card = 3 ∧ (cubeClass v b).card = 3 ∧
      (∑ i ∈ cubeClass v a, v i) = 0 ∧ (∑ i ∈ cubeClass v b, v i) = 0 := by
  classical
  let A := cubeClass v a
  have hAcube : ∀ i ∈ A, v i ^ 3 = a := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hBcube : ∀ i ∈ Aᶜ, v i ^ 3 = b := by
    intro i hi
    have hnot : v i ^ 3 ≠ a := by simpa [A, cubeClass] using hi
    exact (hvalues i).resolve_left hnot
  have hB : Aᶜ = cubeClass v b := by
    ext i
    simp only [cubeClass, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hBcube i
    · intro hi
      have hnot : v i ^ 3 ≠ a := by
        intro heq
        exact hab (heq.symm.trans hi)
      simpa [A, cubeClass] using hnot
  let qa := ∑ i ∈ A, (conj (v i)) ^ 2
  let qb := ∑ i ∈ Aᶜ, (conj (v i)) ^ 2
  have hqa : (∑ i ∈ A, v i) = a * qa := by
    dsimp [qa]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := unit_cube_mul_conj_square (hv i)
    rw [hAcube i hi] at hu
    exact hu.symm
  have hqb : (∑ i ∈ Aᶜ, v i) = b * qb := by
    dsimp [qb]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := unit_cube_mul_conj_square (hv i)
    rw [hBcube i hi] at hu
    exact hu.symm
  have hq : qa + qb = 0 := by
    calc
      qa + qb = ∑ i, (conj (v i)) ^ 2 :=
        Finset.sum_add_sum_compl A (fun i => (conj (v i)) ^ 2)
      _ = conj (∑ i, v i ^ 2) := by simp
      _ = 0 := by rw [h2, map_zero]
  have hp : a * qa + b * qb = 0 := by
    rw [← hqa, ← hqb, Finset.sum_add_sum_compl, h1]
  have hprod : (a - b) * qa = 0 := by linear_combination hp - b * hq
  have hqa0 : qa = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab)
  have hqb0 : qb = 0 := by linear_combination hq - hqa0
  have hsumA : (∑ i ∈ A, v i) = 0 := by rw [hqa, hqa0, mul_zero]
  have hsumB : (∑ i ∈ Aᶜ, v i) = 0 := by rw [hqb, hqb0, mul_zero]
  have hia0 : v ia ≠ 0 := by
    intro h
    have hunit := hv ia
    simp [h] at hunit
  have hib0 : v ib ≠ 0 := by
    intro h
    have hunit := hv ib
    simp [h] at hunit
  have ha : a ≠ 0 := hia ▸ pow_ne_zero 3 hia0
  have hb : b ≠ 0 := hib ▸ pow_ne_zero 3 hib0
  have hneA : A.Nonempty := ⟨ia, by simp [A, cubeClass, hia]⟩
  have hneB : (Aᶜ).Nonempty := by
    refine ⟨ib, ?_⟩
    simp [A, cubeClass, hib, Ne.symm hab]
  have hcardA := same_cube_zero_sum_card_ge_three v A a ha hneA hAcube hsumA
  have hcardB := same_cube_zero_sum_card_ge_three v Aᶜ b hb hneB hBcube hsumB
  have hbound : A.card ≤ 6 := by simpa using Finset.card_le_univ A
  have hcompl : (Aᶜ).card = 6 - A.card := by simpa using Finset.card_compl A
  have heqA : A.card = 3 := by omega
  have heqB : (Aᶜ).card = 3 := by omega
  exact ⟨heqA, hB ▸ heqB, hsumA, hB ▸ hsumB⟩

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicPrelim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Characteristic-polynomial reduction for the cubic classification in §3. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem characteristic_polynomial_expansion (v : (Fin 6) → ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (v i))) =
      ∑ j ∈ Finset.range 7,
        (-1 : Polynomial ℂ) ^ j *
          (Polynomial.C (elementarySum v j) * Polynomial.X ^ (6 - j)) := by
  have h := Multiset.prod_X_sub_X_eq_sum_esymm
    ((Finset.univ : Finset (Fin 6)).val.map v)
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val,
    Finset.esymm_map_val, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Fintype.card_fin, elementarySum] using h

/-- Unit entries with first and second power sums zero have a characteristic
polynomial depending only on `X³`, as used at the start of cubic classification. -/
theorem characteristic_polynomial_in_cubes (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    (∏ i, (Polynomial.X - Polynomial.C (v i))) =
      Polynomial.X ^ 6 - Polynomial.C (elementarySum v 3) * Polynomial.X ^ 3 +
        Polynomial.C (∏ i, v i) := by
  obtain ⟨he1, he2⟩ := elementarySum_one_two_zero v h1 h2
  obtain ⟨he4, he5⟩ := elementarySum_four_five_zero v hv h1 h2
  rw [characteristic_polynomial_expansion]
  simp [Finset.sum_range_succ, elementarySum_zero, elementarySum_six,
    he1, he2, he4, he5]
  ring

theorem cubed_entry_quadratic (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) (i : (Fin 6)) :
    (v i ^ 3) ^ 2 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) = 0 := by
  have h := congrArg (Polynomial.eval (v i))
    (characteristic_polynomial_in_cubes v hv h1 h2)
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul] at h
  have hz : (∏ j, (v i - v j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (v i))
  rw [hz] at h
  calc
    (v i ^ 3) ^ 2 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) =
        v i ^ 6 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) := by ring
    _ = 0 := h.symm

theorem quadratic_two_values {a b c s p : ℂ}
    (ha : a ^ 2 - s * a + p = 0) (hb : b ^ 2 - s * b + p = 0)
    (hc : c ^ 2 - s * c + p = 0) (hab : a ≠ b) : c = a ∨ c = b := by
  have hprod : (a - b) * (a + b - s) = 0 := by linear_combination ha - hb
  have hsum : a + b - s = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab)
  have hs : s = a + b := by linear_combination -hsum
  have hp : p = a * b := by rw [hs] at ha; linear_combination ha
  rw [hs, hp] at hc
  have hfactor : (c - a) * (c - b) = 0 := by linear_combination hc
  simpa only [sub_eq_zero] using (mul_eq_zero.mp hfactor)

/-- This gives the first, algebraic part of the two-triples conclusion.
The multiplicity statement is a separate obligation. -/
theorem cube_values_at_most_two (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    ∃ a b : ℂ, ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b := by
  classical
  by_cases h : ∀ i, v i ^ 3 = v 0 ^ 3
  · exact ⟨v 0 ^ 3, v 0 ^ 3, fun i => Or.inl (h i)⟩
  · obtain ⟨j, hj⟩ := not_forall.mp h
    refine ⟨v 0 ^ 3, v j ^ 3, fun i => ?_⟩
    exact quadratic_two_values
      (cubed_entry_quadratic v hv h1 h2 0)
      (cubed_entry_quadratic v hv h1 h2 j)
      (cubed_entry_quadratic v hv h1 h2 i) (Ne.symm hj)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSupportBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem cubed_entries_twoValuePattern (v : Fin 6 → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    TwoValuePattern (fun i => v i ^ 3) := by
  classical
  have ht := cube_values_at_most_two v hv h1 h2
  refine ⟨ht, ?_⟩
  intro a ha hb
  obtain ⟨ia, hia⟩ := ha
  obtain ⟨ib, hib⟩ := hb
  change v ia ^ 3 = a at hia
  change v ib ^ 3 ≠ a at hib
  have hne : v ia ^ 3 ≠ v ib ^ 3 := by rw [hia]; exact Ne.symm hib
  have hvalues : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = v ib ^ 3 := by
    simpa [hia] using value_pair_exhausts (fun i => v i ^ 3) ht ia ib hne
  have hc := two_cube_classes_card_three v hv h1 h2 a (v ib ^ 3)
    (Ne.symm hib) hvalues ia ib hia rfl
  exact hc.1

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

theorem character_permutation (x : Coord → ℂ) (π : Equiv.Perm Coord) (a : Charge) :
    character (x ∘ π) a = character x (permuteCharge π.symm a) := by
  unfold character permuteCharge
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp π (fun i => x i ^ a (π.symm i))

theorem g_row_permutation (H : CMatrix) (π : Equiv.Perm Coord) (a : Charge) :
    g (fun i j => H (π i) j) a = g H (permuteCharge π.symm a) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact character_permutation (fun i => H i k) π a

theorem equivalent_trans {H K L : CMatrix} (h₁ : Equivalent H K)
    (h₂ : Equivalent K L) : Equivalent H L := by
  rcases h₁ with ⟨r, c, u, v, hu, hv, h₁⟩
  rcases h₂ with ⟨r', c', u', v', hu', hv', h₂⟩
  refine ⟨r'.trans r, c'.trans c, (fun i => u' i * u (r' i)),
    (fun j => v (c' j) * v' j), ?_, ?_, ?_⟩
  · intro i
    simp [map_mul, hu, hu']
  · intro j
    simp [map_mul, hv, hv']
  · intro i j
    rw [h₂, h₁]
    simp [mul_assoc]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicHadamard
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem hadamard_row_ratio_moments {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (r s : Coord) (hrs : r ≠ s) :
    (∀ j, Complex.normSq (H r j / H s j) = 1) ∧
      (∑ j, H r j / H s j) = 0 ∧ (∑ j, (H r j / H s j) ^ 2) = 0 := by
  refine ⟨fun j => ?_, ?_, ?_⟩
  · simp [hH.1]
  · simp_rw [div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)]
    simpa [hrs] using hH.row_orthogonal r s
  · have he (j : Coord) : (H r j / H s j) ^ 2 =
        H r j ^ 2 * conj (H s j ^ 2) := by
      rw [div_pow, div_eq_mul_inv, unit_inv_eq_conj (hH2.1 s j)]
    simp_rw [he]
    simpa [hrs] using hH2.row_orthogonal r s

theorem cubed_row_ratio_pattern {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (r s : Coord) (hrs : r ≠ s) :
    TwoValuePattern (fun j => H r j ^ 3 / H s j ^ 3) := by
  obtain ⟨hu, h1, h2⟩ := hadamard_row_ratio_moments hH hH2 r s hrs
  simpa only [div_pow] using cubed_entries_twoValuePattern
    (fun j => H r j / H s j) hu h1 h2

theorem twoValuePattern_constant (a : ℂ) : TwoValuePattern (fun _ : Coord => a) := by
  refine ⟨⟨a, a, fun _ => Or.inl rfl⟩, ?_⟩
  intro b ⟨i, hi⟩ ⟨j, hj⟩
  exact False.elim (hj hi)

theorem cubed_row_pattern {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (h0 : ∀ j, H 0 j = 1)
    (r : Coord) : TwoValuePattern (fun j => H r j ^ 3) := by
  by_cases hr : r = 0
  · subst r
    simpa only [h0, one_pow] using twoValuePattern_constant 1
  · simpa only [h0, one_pow, div_one] using cubed_row_ratio_pattern hH hH2 r 0 hr

/-- Before excluding it with the three-by-three block obstruction, the only
possible failure of cube roots after dephasing has one constant block. -/
theorem dephased_hadamard_cubes_block {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1)
    (i j : Coord) (hij : H i j ^ 3 ≠ 1) :
    ∃ (R S : Finset Coord) (x : ℂ),
      R.card = 3 ∧ S.card = 3 ∧ (0 : Coord) ∉ R ∧ (0 : Coord) ∉ S ∧
      x ≠ 0 ∧ x ≠ 1 ∧
      ∀ r c, H r c ^ 3 = if r ∈ R ∧ c ∈ S then x else 1 := by
  apply dephased_pattern_single_block (fun r c => H r c ^ 3)
    (fun j => by rw [h0row, one_pow]) (fun i => by rw [h0col, one_pow])
    (fun r c => pow_ne_zero _ (unit_ne_zero (hH.1 r c)))
    (cubed_row_pattern hH hH2 h0row) ?_
    (cubed_row_ratio_pattern hH hH2) i j hij
  intro c
  exact cubed_row_pattern hH.transpose hH2.transpose h0col c

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicExclusion
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sum_enumerateThree (S : Finset Coord) (hS : S.card = 3) (f : Coord → ℂ) :
    (∑ i, f (enumerateThree S hS i)) = ∑ i ∈ S, f i := by
  rw [← Finset.sum_coe_sort S f]
  exact Equiv.sum_comp (enumerateThree S hS) (fun i : S => f i)

theorem no_hadamard_orthogonal_restrictions {H : CMatrix} (hH : IsHadamard H)
    (R S : Finset Coord) (hR : R.card = 3) (hS : S.card = 3)
    (hcross : ∀ r ∈ R, ∀ s ∈ Rᶜ, ∑ c ∈ S, H r c * conj (H s c) = 0) : False := by
  have hRc : Rᶜ.card = 3 := by simp [Finset.card_compl, hR]
  let r := enumerateThree R hR
  let s := enumerateThree Rᶜ hRc
  let c := enumerateThree S hS
  let A : Matrix (Fin 3) (Fin 3) ℂ := fun i j => H (r i) (c j)
  let B : Matrix (Fin 3) (Fin 3) ℂ := fun i j => H (s i) (c j)
  apply no_cubic_three_by_three_block A B (fun i j => hH.1 _ _) ?_ ?_
  · ext i j
    change (∑ k, H (r i) (c k) * conj (H (s j) (c k))) = 0
    rw [sum_enumerateThree S hS (fun k => H (r i) k * conj (H (s j) k))]
    exact hcross (r i) (r i).property (s j) (s j).property
  · ext i j
    change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) +
        (∑ k, conj (H (s k) (c i)) * H (s k) (c j)) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [sum_enumerateThree R hR (fun k => conj (H k (c i)) * H k (c j)),
      sum_enumerateThree Rᶜ hRc (fun k => conj (H k (c i)) * H k (c j)),
      Finset.sum_add_sum_compl, hH.column_orthogonal]
    by_cases hij : i = j
    · simp [hij]
    · have hc : (c i : Coord) ≠ c j := by
        intro h
        exact hij (c.injective (Subtype.ext h))
      simp [hij, hc]

theorem cubic_block_cross_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (R S : Finset Coord) (hS : S.card = 3) (x : ℂ) (hx : x ≠ 1)
    (hblock : ∀ r c, H r c ^ 3 = if r ∈ R ∧ c ∈ S then x else 1)
    (r : Coord) (hr : r ∈ R) (s : Coord) (hs : s ∈ Rᶜ) :
    ∑ c ∈ S, H r c * conj (H s c) = 0 := by
  classical
  have hsR : s ∉ R := Finset.mem_compl.mp hs
  have hrs : r ≠ s := by intro h; exact hsR (h ▸ hr)
  let v : Coord → ℂ := fun c => H r c / H s c
  obtain ⟨hu, h1, h2⟩ := hadamard_row_ratio_moments hH hH2 r s hrs
  have hv (c : Coord) : v c ^ 3 = if c ∈ S then x else 1 := by
    by_cases hc : c ∈ S <;> simp [v, div_pow, hblock, hr, hsR, hc]
  have hvalues : ∀ c, v c ^ 3 = x ∨ v c ^ 3 = 1 := by
    intro c
    by_cases hc : c ∈ S <;> simp [hv, hc]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hSc : Sᶜ.card = 3 := by simp [Finset.card_compl, hS]
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < Sᶜ.card by omega)
  have hav : v a ^ 3 = x := by simp [hv, ha]
  have hbv : v b ^ 3 = 1 := by simp [hv, Finset.mem_compl.mp hb]
  have hm := two_cube_classes_card_three v hu h1 h2 x 1 hx hvalues a b hav hbv
  have hset : cubeClass v x = S := by
    ext c
    by_cases hc : c ∈ S <;> simp [cubeClass, hv, hc, Ne.symm hx]
  have hz : (∑ c ∈ S, v c) = 0 := by simpa only [hset] using hm.2.2.1
  simpa only [v, div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)] using hz

/-- An arbitrary dephased complex Hadamard matrix whose entrywise square is
Hadamard has only cube roots of unity as entries. -/
theorem dephased_hadamard_cubes_one {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) :
    ∀ i j, H i j ^ 3 = 1 := by
  intro i j
  by_contra hij
  obtain ⟨R, S, x, hR, hS, _, _, _, hx, hblock⟩ :=
    dephased_hadamard_cubes_block hH hH2 h0row h0col i j hij
  exact no_hadamard_orthogonal_restrictions hH R S hR hS
    (cubic_block_cross_orthogonal hH hH2 R S hS x hx hblock)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_Tao
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit five-cycle representative of Tao's cubic matrix. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 3 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 3 (by decide)

theorem omega_cube : omega ^ 3 = 1 := omega_isPrimitiveRoot.pow_eq_one

theorem omega_norm : ‖omega‖ = 1 :=
  omega_isPrimitiveRoot.norm'_eq_one (by decide)

theorem omega_normSq : Complex.normSq omega = 1 := by
  rw [Complex.normSq_eq_norm_sq, omega_norm]
  norm_num

theorem omega_sum : 1 + omega + omega ^ 2 = 0 := by
  simpa [Finset.sum_range_succ] using
    omega_isPrimitiveRoot.geom_sum_eq_zero (by decide : 1 < 3)

theorem omega_conj : conj omega = omega ^ 2 := by
  have homega : omega ≠ 0 := by
    intro hzero
    simpa [hzero] using omega_normSq
  apply mul_left_cancel₀ homega
  calc
    omega * conj omega = 1 := by simp [Complex.mul_conj, omega_normSq]
    _ = omega * omega ^ 2 := by rw [← pow_succ', omega_cube]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicRoots
attribute [-simp] _root_.OAI.MUB6.character_zero _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.g_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem omega_ne_one : omega ≠ 1 := omega_isPrimitiveRoot.ne_one (by decide)

theorem omega_sq_ne_one : omega ^ 2 ≠ 1 := by
  intro h
  have he : omega ^ 3 = omega := by rw [pow_succ, h, one_mul]
  exact omega_ne_one (he.symm.trans omega_cube)

theorem omega_sq_ne_omega : omega ^ 2 ≠ omega := by
  intro h
  have he : omega * omega = omega * 1 := by simpa [pow_two] using h
  exact omega_ne_one (mul_left_cancel₀ (omega_isPrimitiveRoot.ne_zero (by decide)) he)

theorem omega_re : omega.re = (-1 / 2 : ℝ) := by
  have h := congrArg Complex.re omega_sum
  rw [← omega_conj] at h
  simp only [Complex.add_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at h
  linarith

theorem omega_sq_re : (omega ^ 2).re = (-1 / 2 : ℝ) := by
  rw [← omega_conj, Complex.conj_re, omega_re]

theorem cube_roots_three (z : ℂ) (hz : z ^ 3 = 1) :
    z = 1 ∨ z = omega ∨ z = omega ^ 2 := by
  have hf : (z - 1) * (z - omega) * (z - omega ^ 2) = 0 := by
    calc
      (z - 1) * (z - omega) * (z - omega ^ 2) = z ^ 3 - 1 := by
        linear_combination (-z ^ 2 + z) * omega_sum + (z - 1) * omega_cube
      _ = 0 := by rw [hz, sub_self]
  rcases mul_eq_zero.mp hf with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem cube_root_real_indicator (z : ℂ) (hz : z ^ 3 = 1) :
    z.re = (3 / 2 : ℝ) * (if z = 1 then 1 else 0) - 1 / 2 := by
  rcases cube_roots_three z hz with rfl | rfl | rfl
  · norm_num
  · rw [ite_eq_right omega_ne_one, omega_re]
    norm_num
  · rw [ite_eq_right omega_sq_ne_one, omega_sq_re]
    norm_num

/-- Six cube roots summing to zero contain the root one exactly twice. -/
theorem cube_roots_one_count (v : Coord → ℂ) (hv : ∀ i, v i ^ 3 = 1)
    (hs : ∑ i, v i = 0) : (Finset.univ.filter (fun i => v i = 1)).card = 2 := by
  classical
  have hre : (∑ i, (v i).re) = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hs
  simp_rw [cube_root_real_indicator _ (hv _)] at hre
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hre
  have hc : (∑ i, if v i = 1 then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => v i = 1)).card : ℝ) := by simp
  rw [hc] at hre
  norm_num at hre
  have hn : ((Finset.univ.filter (fun i => v i = 1)).card : ℝ) = 2 := by
    linarith
  exact_mod_cast hn

/-- Every cube root occurs twice among six cube roots whose sum vanishes. -/
theorem cube_roots_each_count (v : Coord → ℂ) (hv : ∀ i, v i ^ 3 = 1)
    (hs : ∑ i, v i = 0) (a : ℂ) (ha : a ^ 3 = 1) :
    (Finset.univ.filter (fun i => v i = a)).card = 2 := by
  classical
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hv' : ∀ i, (v i / a) ^ 3 = 1 := by intro i; rw [div_pow, hv, ha, div_self one_ne_zero]
  have hs' : (∑ i, v i / a) = 0 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hs, zero_mul]
  have hc := cube_roots_one_count (fun i => v i / a) hv' hs'
  simpa only [div_eq_one_iff_eq ha0] using hc

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicMatching
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem cubic_hadamard_row_sum {H : CMatrix} (hH : IsHadamard H)
    (h0row : ∀ j, H 0 j = 1) (r : Coord) (hr : r ≠ 0) : ∑ j, H r j = 0 := by
  simpa [h0row, hr] using hH.row_orthogonal r 0

theorem cubic_hadamard_row_one_count {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) (r : Fin 5) :
    (Finset.univ.filter (fun j : Fin 5 => H r.succ j.succ = 1)).card = 1 := by
  classical
  have hc := cube_roots_one_count (fun j => H r.succ j) (hcube r.succ)
    (cubic_hadamard_row_sum hH h0row r.succ (Fin.succ_ne_zero _))
  rw [Fin.card_filter_univ_succ] at hc
  simp only [h0col, ite_true, if_true] at hc
  omega

theorem existsUnique_of_filter_card_one (p : Fin 5 → Prop) [DecidablePred p]
    (hc : (Finset.univ.filter p).card = 1) : ∃! i, p i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hmem : ∀ j, p j ↔ j = i := by
    intro j
    have hh := congrArg (fun S : Finset (Fin 5) => j ∈ S) hi
    simpa using hh
  exact ⟨i, (hmem i).mpr rfl, fun j hj => (hmem j).mp hj⟩

/-- The noninitial entries equal to one form a perfect matching. -/
theorem cubic_hadamard_one_matching {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) :
    ∃ p : Equiv.Perm (Fin 5), ∀ i j, H i.succ (p j).succ = 1 ↔ i = j := by
  classical
  have hrow : ∀ i : Fin 5, ∃! j : Fin 5, H i.succ j.succ = 1 := fun i =>
    existsUnique_of_filter_card_one _ (cubic_hadamard_row_one_count hH hcube h0row h0col i)
  have hcol : ∀ j : Fin 5, ∃! i : Fin 5, H i.succ j.succ = 1 := fun j =>
    existsUnique_of_filter_card_one _
      (cubic_hadamard_row_one_count hH.transpose (fun i j => hcube j i) h0col h0row j)
  choose f hf huniq using hrow
  have hinj : Function.Injective f := by
    intro i j hij
    exact (hcol (f i)).unique (hf i) (by rw [hij]; exact hf j)
  let p : Equiv.Perm (Fin 5) :=
    Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨p, fun i j => ?_⟩
  constructor
  · intro hij
    have h : f j = f i := huniq i (f j) hij
    exact (hinj h).symm
  · rintro rfl
    exact hf i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicGraph
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem cubic_graph_entry {H : CMatrix} (hcube : ∀ i j, H i j ^ 3 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j) (i j : Fin 5) :
    H i.succ j.succ = if i = j then 1 else
      if cubicGraph H i j then omega else omega ^ 2 := by
  classical
  by_cases hij : i = j
  · simp [hij, (hdiag j j).mpr rfl]
  · have hne : H i.succ j.succ ≠ 1 := fun h => hij ((hdiag i j).mp h)
    rcases cube_roots_three _ (hcube i.succ j.succ) with h | h | h
    · exact False.elim (hne h)
    · simp [hij, cubicGraph, h]
    · simp [hij, cubicGraph, h, omega_sq_ne_omega]

theorem cubic_graph_degree {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) (i : Fin 5) :
    (Finset.univ.filter (fun j => cubicGraph H i j = true)).card = 2 := by
  classical
  have hc := cube_roots_each_count (fun j => H i.succ j) (hcube i.succ)
    (cubic_hadamard_row_sum hH h0row i.succ (Fin.succ_ne_zero _)) omega omega_cube
  rw [Fin.card_filter_univ_succ] at hc
  simpa [h0col, Ne.symm omega_ne_one, cubicGraph] using hc

theorem cubic_rows_agree_two {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1) (r s : Coord) (hrs : r ≠ s) :
    (Finset.univ.filter (fun j => H r j = H s j)).card = 2 := by
  classical
  have hv : ∀ j, (H r j / H s j) ^ 3 = 1 := by intro j; simp [div_pow, hcube]
  have hs : (∑ j, H r j / H s j) = 0 := by
    simp_rw [div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)]
    simpa [hrs] using hH.row_orthogonal r s
  have hc := cube_roots_one_count (fun j => H r j / H s j) hv hs
  simpa only [div_eq_one_iff_eq (unit_ne_zero (hH.1 s _))] using hc

theorem cubic_graph_agreement {H : CMatrix} (hcube : ∀ i j, H i j ^ 3 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j)
    (i j : Fin 5) (hij : i ≠ j) (k : Fin 5) :
    H i.succ k.succ = H j.succ k.succ ↔
      k ≠ i ∧ k ≠ j ∧ cubicGraph H i k = cubicGraph H j k := by
  by_cases hki : k = i
  · subst k
    have hji : H j.succ i.succ ≠ 1 := fun h => hij ((hdiag j i).mp h).symm
    simp [(hdiag i i).mpr rfl, Ne.symm hji]
  by_cases hkj : k = j
  · subst k
    simp [(hdiag j j).mpr rfl, (hdiag i j), hij]
  rw [cubic_graph_entry hcube hdiag i k, cubic_graph_entry hcube hdiag j k]
  cases hi : cubicGraph H i k <;> cases hj : cubicGraph H j k <;>
    simp [hki, hkj, Ne.symm hki, Ne.symm hkj,
      omega_sq_ne_omega, Ne.symm omega_sq_ne_omega]

theorem cubic_graph_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1) (h0col : ∀ i, H i 0 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j)
    (i j : Fin 5) (hij : i ≠ j) :
    (Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧
      cubicGraph H i k = cubicGraph H j k)).card = 1 := by
  classical
  have hc := cubic_rows_agree_two hH hcube i.succ j.succ
    (fun h => hij (Fin.succ_injective _ h))
  rw [Fin.card_filter_univ_succ] at hc
  simp only [h0col, ite_true, if_true] at hc
  simp_rw [cubic_graph_agreement hcube hdiag i j hij] at hc
  omega

theorem tao_noninitial (i j : Fin 5) :
    tao i.succ j.succ = if i = j then 1 else
      if canonicalFiveCycle i j then omega else omega ^ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [tao, taoExponent, canonicalFiveCycle, fiveGraph]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_NormalizedCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A second finite presentation of the five-cycle classification.  A row has
two positive signs among four off-diagonal positions, hence six choices. -/

namespace MUB6

theorem rowChoice_complete : ∀ (i : Fin 5) (f : Fin 5 → Bool),
    f i = false → (Finset.univ.filter (fun j => f j = true)).card = 2 →
      ∃ a, ∀ j, fiveRowChoice i a j = f j := by
  decide +kernel

private theorem normalizedCodes_00 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_01 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_02 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_03 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_04 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_05 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_10 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_11 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_12 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_13 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_14 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_15 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_20 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_21 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_22 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_23 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_24 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_25 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_30 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_31 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_32 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_33 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_34 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_35 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_40 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_41 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_42 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_43 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_44 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_45 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_50 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_51 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_52 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_53 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_54 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_55 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

theorem normalizedCodes_classified (a : Fin 5 → Fin 6) : normalizedCodeClassified a := by
  have h (a0 a1 a2 a3 a4 : Fin 6) : normalizedCodeClassified ![a0, a1, a2, a3, a4] := by
    fin_cases a0 <;> fin_cases a1
    · exact normalizedCodes_00 a2 a3 a4
    · exact normalizedCodes_01 a2 a3 a4
    · exact normalizedCodes_02 a2 a3 a4
    · exact normalizedCodes_03 a2 a3 a4
    · exact normalizedCodes_04 a2 a3 a4
    · exact normalizedCodes_05 a2 a3 a4
    · exact normalizedCodes_10 a2 a3 a4
    · exact normalizedCodes_11 a2 a3 a4
    · exact normalizedCodes_12 a2 a3 a4
    · exact normalizedCodes_13 a2 a3 a4
    · exact normalizedCodes_14 a2 a3 a4
    · exact normalizedCodes_15 a2 a3 a4
    · exact normalizedCodes_20 a2 a3 a4
    · exact normalizedCodes_21 a2 a3 a4
    · exact normalizedCodes_22 a2 a3 a4
    · exact normalizedCodes_23 a2 a3 a4
    · exact normalizedCodes_24 a2 a3 a4
    · exact normalizedCodes_25 a2 a3 a4
    · exact normalizedCodes_30 a2 a3 a4
    · exact normalizedCodes_31 a2 a3 a4
    · exact normalizedCodes_32 a2 a3 a4
    · exact normalizedCodes_33 a2 a3 a4
    · exact normalizedCodes_34 a2 a3 a4
    · exact normalizedCodes_35 a2 a3 a4
    · exact normalizedCodes_40 a2 a3 a4
    · exact normalizedCodes_41 a2 a3 a4
    · exact normalizedCodes_42 a2 a3 a4
    · exact normalizedCodes_43 a2 a3 a4
    · exact normalizedCodes_44 a2 a3 a4
    · exact normalizedCodes_45 a2 a3 a4
    · exact normalizedCodes_50 a2 a3 a4
    · exact normalizedCodes_51 a2 a3 a4
    · exact normalizedCodes_52 a2 a3 a4
    · exact normalizedCodes_53 a2 a3 a4
    · exact normalizedCodes_54 a2 a3 a4
    · exact normalizedCodes_55 a2 a3 a4
  have he : a = ![a 0, a 1, a 2, a 3, a 4] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact h _ _ _ _ _

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_NormalizedCubic
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem normalized_cubic_equivalent_tao {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j) : Equivalent H tao := by
  classical
  have hchoice (i : Fin 5) : ∃ a, ∀ j, fiveRowChoice i a j = cubicGraph H i j := by
    apply rowChoice_complete i (cubicGraph H i) ?_ (cubic_graph_degree hH hcube h0row h0col i)
    simp [cubicGraph, (hdiag i i).mpr rfl, Ne.symm omega_ne_one]
  choose a ha using hchoice
  have hagree : ∀ i j, normalizedCodeGraph a i j = cubicGraph H i j := ha
  have horth : normalizedCodeOrthogonal a := by
    intro i j hij
    simpa only [hagree] using cubic_graph_orthogonal hH hcube h0col hdiag i j hij
  obtain ⟨c, hc⟩ := normalizedCodes_classified a horth
  let q := fiveCyclePermutation c
  have hq (i j : Fin 5) : cubicGraph H (q i) (q j) = canonicalFiveCycle i j := by
    simpa only [q, fiveCyclePermutation, Equiv.ofBijective_apply, hagree] using hc i j
  have heq (i j : Coord) : H (fixZeroPermutation q i) (fixZeroPermutation q j) = tao i j := by
    cases i using Fin.cases with
    | zero => fin_cases j <;> simp [h0row, tao, taoExponent]
    | succ i =>
      cases j using Fin.cases with
      | zero => fin_cases i <;> simp [h0col, tao, taoExponent]
      | succ j =>
        simp only [fixZeroPermutation_succ, cubic_graph_entry hcube hdiag, hq,
          Equiv.apply_eq_iff_eq, tao_noninitial]
  refine ⟨fixZeroPermutation q, fixZeroPermutation q, fun _ => 1, fun _ => 1,
    by simp, by simp, ?_⟩
  intro i j
  simpa using (heq i j).symm

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Equivalence
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem IsHadamard.phaseTransform {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (hu : ∀ i, Complex.normSq (u i) = 1)
    (hv : ∀ j, Complex.normSq (v j) = 1) : IsHadamard (phaseTransform H u v) := by
  refine ⟨?_, ?_⟩
  · intro i j
    change Complex.normSq (u i * H i j * v j) = 1
    simp [map_mul, hu, hv, hH.1]
  · ext i j
    have hsum : (∑ k, conj (MUB6.phaseTransform H u v k i) * MUB6.phaseTransform H u v k j) =
        conj (v i) * v j * ∑ k, conj (H k i) * H k j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have huk : conj (u k) * u k = 1 := by
        rw [mul_comm, Complex.mul_conj, hu]
        rfl
      simp only [MUB6.phaseTransform, map_mul]
      calc
        _ = (conj (u k) * u k) *
          (conj (v i) * v j * (conj (H k i) * H k j)) := by ring
        _ = _ := by rw [huk, one_mul]
    change (∑ k, conj (MUB6.phaseTransform H u v k i) * MUB6.phaseTransform H u v k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [hsum, hH.column_orthogonal]
    by_cases hij : i = j
    · subst j
      rw [mul_comm (conj (v i)) (v i), Complex.mul_conj, hv]
      simp
    · simp [hij]

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

theorem Equivalent.isHadamard {H K : CMatrix} (h : Equivalent H K)
    (hH : IsHadamard H) : IsHadamard K := by
  rcases h with ⟨r, c, u, v, hu, hv, he⟩
  have hK : K = phaseTransform (fun i j => H (r i) (c j)) u v := by
    ext i j
    exact he i j
  rw [hK]
  exact (hH.permutations r c).phaseTransform u v hu hv

theorem dephase_equivalent {H : CMatrix} (hH : IsHadamard H) :
    Equivalent H (dephase H) := by
  refine ⟨Equiv.refl _, Equiv.refl _, (fun i => (H i 0)⁻¹),
    (fun j => H 0 0 * (H 0 j)⁻¹), ?_, ?_, ?_⟩
  · intro i
    simp [hH.1]
  · intro j
    simp [map_mul, hH.1]
  · intro i j
    rfl

theorem dephase_isHadamard {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard (dephase H) := (dephase_equivalent hH).isHadamard hH

theorem dephase_row_zero {H : CMatrix} (hH : IsHadamard H) (j : Coord) :
    dephase H 0 j = 1 := by
  unfold dephase phaseTransform
  field_simp [unit_ne_zero (hH.1 0 0), unit_ne_zero (hH.1 0 j)]

theorem dephase_column_zero {H : CMatrix} (hH : IsHadamard H) (i : Coord) :
    dephase H i 0 = 1 := by
  unfold dephase phaseTransform
  field_simp [unit_ne_zero (hH.1 0 0), unit_ne_zero (hH.1 i 0)]

theorem equivalent_squares {H K : CMatrix} (h : Equivalent H K) :
    Equivalent (fun i j => H i j ^ 2) (fun i j => K i j ^ 2) := by
  rcases h with ⟨r, c, u, v, hu, hv, he⟩
  refine ⟨r, c, (fun i => u i ^ 2), (fun j => v j ^ 2), ?_, ?_, ?_⟩
  · intro i
    simp [map_pow, hu]
  · intro j
    simp [map_pow, hv]
  · intro i j
    change K i j ^ 2 = u i ^ 2 * H (r i) (c j) ^ 2 * v j ^ 2
    rw [he]
    ring

theorem dephase_square_isHadamard {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) :
    IsHadamard (fun i j => dephase H i j ^ 2) :=
  (equivalent_squares (dephase_equivalent hH)).isHadamard hH2

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicClassification
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

/-- The cubic classification from the companion: no restriction is imposed
on the complex entries or on the unit phases in the equivalence relation. -/
theorem hadamard_square_equivalent_tao {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) : Equivalent H tao := by
  let D := dephase H
  have hD : IsHadamard D := dephase_isHadamard hH
  have hD2 : IsHadamard (fun i j => D i j ^ 2) := dephase_square_isHadamard hH hH2
  have hDr : ∀ j, D 0 j = 1 := dephase_row_zero hH
  have hDc : ∀ i, D i 0 = 1 := dephase_column_zero hH
  have hcube : ∀ i j, D i j ^ 3 = 1 := dephased_hadamard_cubes_one hD hD2 hDr hDc
  obtain ⟨p, hp⟩ := cubic_hadamard_one_matching hD hcube hDr hDc
  let K : CMatrix := fun i j => D i (fixZeroPermutation p j)
  have hK : IsHadamard K := by
    simpa only [Equiv.refl_apply] using hD.permutations (Equiv.refl _) (fixZeroPermutation p)
  have hKr : ∀ j, K 0 j = 1 := fun j => hDr _
  have hKc : ∀ i, K i 0 = 1 := fun i => hDc _
  have hKcube : ∀ i j, K i j ^ 3 = 1 := fun i j => hcube _ _
  have hdiag : ∀ i j : Fin 5, K i.succ j.succ = 1 ↔ i = j := hp
  have hDK : Equivalent D K := by
    refine ⟨Equiv.refl _, fixZeroPermutation p, fun _ => 1, fun _ => 1,
      by simp, by simp, ?_⟩
    intro i j
    simp [K]
  exact equivalent_trans (dephase_equivalent hH)
    (equivalent_trans hDK (normalized_cubic_equivalent_tao hK hKcube hKr hKc hdiag))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Square
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem isHadamard_of_row_gram (H : CMatrix)
    (hu : ∀ i j, Complex.normSq (H i j) = 1)
    (hr : H * H.conjTranspose = (6 : ℂ) • (1 : CMatrix)) : IsHadamard H := by
  refine ⟨hu, ?_⟩
  have hi : H * ((6 : ℂ)⁻¹ • H.conjTranspose) = (1 : CMatrix) := by
    rw [Matrix.mul_smul, hr, smul_smul]
    norm_num
  have hc := mul_eq_one_comm.mp hi
  rw [Matrix.smul_mul] at hc
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hc
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem character_doubleDifference (x : Coord → ℂ)
    (hx : ∀ k, Complex.normSq (x k) = 1) (i j : Coord) :
    character x (doubleDifference i j) = x i ^ 2 * conj (x j ^ 2) := by
  rw [doubleDifference, character_add x (fun k => unit_ne_zero (hx k)),
    character_difference x hx, map_pow]
  ring

theorem g_doubleDifference {H : CMatrix} (hH : IsHadamard H) (i j : Coord) :
    g H (doubleDifference i j) =
      (6 : ℂ)⁻¹ * ∑ k, H i k ^ 2 * conj (H j k ^ 2) := by
  simp only [g, character_doubleDifference _ (fun k => hH.1 k _) i j]

theorem square_isHadamard_of_doubleDifference_zero {H : CMatrix} (hH : IsHadamard H)
    (hz : ∀ i j, i ≠ j → g H (doubleDifference i j) = 0) :
    IsHadamard (fun i j => H i j ^ 2) := by
  have hu : ∀ i j, Complex.normSq (H i j ^ 2) = 1 := by
    intro i j
    simp [map_pow, hH.1]
  apply isHadamard_of_row_gram _ hu
  ext i j
  change (∑ k, H i k ^ 2 * conj (H j k ^ 2)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  by_cases hij : i = j
  · subst j
    simp only [Complex.mul_conj, hu, Complex.ofReal_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one, ite_true, if_true]
  · have h := hz i j hij
    rw [g_doubleDifference hH] at h
    have hs : (∑ k, H i k ^ 2 * conj (H j k ^ 2)) = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    simpa only [hij, ite_false, if_false, mul_zero] using hs

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
attribute [-simp] _root_.OAI.MUB6.average_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_eq_zero_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (h : ∀ i, 0 ≤ f i) : average f = 0 ↔ ∀ i, f i = 0 := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card ι))
  simp only [average, mul_eq_zero, inv_eq_zero, hc, false_or]
  simpa using Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => h i)

theorem average_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∀ i, 0 ≤ f i) : 0 ≤ average f := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => h i))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Moments
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite injective moments of Section 2 of the exact companion.
Both orientations are retained with weight 1/2, including when H = Hᵀ. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem pairAverage_nonneg (H : CMatrix) (F : CMatrix → ℝ)
    (hF : ∀ K, 0 ≤ F K) : 0 ≤ pairAverage H F := by
  apply average_nonneg
  intro π
  exact div_nonneg (add_nonneg (hF _) (hF _)) (by norm_num)

theorem pairAverage_zero_terms (H : CMatrix) (F : CMatrix → ℝ)
    (hF : ∀ K, 0 ≤ F K) (hzero : pairAverage H F = 0) (π : Equiv.Perm Coord) :
    F (fun i j => H (π i) j) = 0 ∧ F (fun i j => H j (π i)) = 0 := by
  have ht := (average_eq_zero_iff _
    (fun p : Equiv.Perm Coord => div_nonneg
      (add_nonneg (hF (fun i j => H (p i) j)) (hF (fun i j => H j (p i))))
      (by norm_num))).mp hzero π
  have h₁ := hF (fun i j => H (π i) j)
  have h₂ := hF (fun i j => H j (π i))
  constructor <;> linarith

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem pair_product_zero_of_certificate {H : CMatrix} {q : Charge}
    (h : PairCertificateIdentity H q) (π : Equiv.Perm Coord) :
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) q = 0 := by
  have hL := pairAverage_nonneg H (fun K => Complex.normSq (pairL K))
    (fun K => Complex.normSq_nonneg _)
  have hg := pairAverage_nonneg H (fun K => Complex.normSq (g K alpha * g K q))
    (fun K => Complex.normSq_nonneg _)
  have hz : pairAverage H (fun K => Complex.normSq (g K alpha * g K q)) = 0 := by
    unfold PairCertificateIdentity at h
    linarith
  have ht := (pairAverage_zero_terms H (fun K => Complex.normSq (g K alpha * g K q))
    (fun K => Complex.normSq_nonneg _) hz π).1
  exact Complex.normSq_eq_zero.mp ht

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairPermutations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6

theorem pairPerm_0_1_witness :
    (permuteCharge pairPerm_0_1.symm alpha = alpha ∨
      permuteCharge pairPerm_0_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_1.symm qCross = doubleDifference 0 1 ∨
      permuteCharge pairPerm_0_1.symm qSame = doubleDifference 0 1) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_0_2_witness :
    (permuteCharge pairPerm_0_2.symm alpha = alpha ∨
      permuteCharge pairPerm_0_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_2.symm qCross = doubleDifference 0 2 ∨
      permuteCharge pairPerm_0_2.symm qSame = doubleDifference 0 2) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_0_3_witness :
    (permuteCharge pairPerm_0_3.symm alpha = alpha ∨
      permuteCharge pairPerm_0_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_3.symm qCross = doubleDifference 0 3 ∨
      permuteCharge pairPerm_0_3.symm qSame = doubleDifference 0 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_0_4_witness :
    (permuteCharge pairPerm_0_4.symm alpha = alpha ∨
      permuteCharge pairPerm_0_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_4.symm qCross = doubleDifference 0 4 ∨
      permuteCharge pairPerm_0_4.symm qSame = doubleDifference 0 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_0_5_witness :
    (permuteCharge pairPerm_0_5.symm alpha = alpha ∨
      permuteCharge pairPerm_0_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_5.symm qCross = doubleDifference 0 5 ∨
      permuteCharge pairPerm_0_5.symm qSame = doubleDifference 0 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_1_0_witness :
    (permuteCharge pairPerm_1_0.symm alpha = alpha ∨
      permuteCharge pairPerm_1_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_0.symm qCross = doubleDifference 1 0 ∨
      permuteCharge pairPerm_1_0.symm qSame = doubleDifference 1 0) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_1_2_witness :
    (permuteCharge pairPerm_1_2.symm alpha = alpha ∨
      permuteCharge pairPerm_1_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_2.symm qCross = doubleDifference 1 2 ∨
      permuteCharge pairPerm_1_2.symm qSame = doubleDifference 1 2) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_1_3_witness :
    (permuteCharge pairPerm_1_3.symm alpha = alpha ∨
      permuteCharge pairPerm_1_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_3.symm qCross = doubleDifference 1 3 ∨
      permuteCharge pairPerm_1_3.symm qSame = doubleDifference 1 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_1_4_witness :
    (permuteCharge pairPerm_1_4.symm alpha = alpha ∨
      permuteCharge pairPerm_1_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_4.symm qCross = doubleDifference 1 4 ∨
      permuteCharge pairPerm_1_4.symm qSame = doubleDifference 1 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_1_5_witness :
    (permuteCharge pairPerm_1_5.symm alpha = alpha ∨
      permuteCharge pairPerm_1_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_5.symm qCross = doubleDifference 1 5 ∨
      permuteCharge pairPerm_1_5.symm qSame = doubleDifference 1 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_2_0_witness :
    (permuteCharge pairPerm_2_0.symm alpha = alpha ∨
      permuteCharge pairPerm_2_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_0.symm qCross = doubleDifference 2 0 ∨
      permuteCharge pairPerm_2_0.symm qSame = doubleDifference 2 0) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_2_1_witness :
    (permuteCharge pairPerm_2_1.symm alpha = alpha ∨
      permuteCharge pairPerm_2_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_1.symm qCross = doubleDifference 2 1 ∨
      permuteCharge pairPerm_2_1.symm qSame = doubleDifference 2 1) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_2_3_witness :
    (permuteCharge pairPerm_2_3.symm alpha = alpha ∨
      permuteCharge pairPerm_2_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_3.symm qCross = doubleDifference 2 3 ∨
      permuteCharge pairPerm_2_3.symm qSame = doubleDifference 2 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_2_4_witness :
    (permuteCharge pairPerm_2_4.symm alpha = alpha ∨
      permuteCharge pairPerm_2_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_4.symm qCross = doubleDifference 2 4 ∨
      permuteCharge pairPerm_2_4.symm qSame = doubleDifference 2 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_2_5_witness :
    (permuteCharge pairPerm_2_5.symm alpha = alpha ∨
      permuteCharge pairPerm_2_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_5.symm qCross = doubleDifference 2 5 ∨
      permuteCharge pairPerm_2_5.symm qSame = doubleDifference 2 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_3_0_witness :
    (permuteCharge pairPerm_3_0.symm alpha = alpha ∨
      permuteCharge pairPerm_3_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_0.symm qCross = doubleDifference 3 0 ∨
      permuteCharge pairPerm_3_0.symm qSame = doubleDifference 3 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_3_1_witness :
    (permuteCharge pairPerm_3_1.symm alpha = alpha ∨
      permuteCharge pairPerm_3_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_1.symm qCross = doubleDifference 3 1 ∨
      permuteCharge pairPerm_3_1.symm qSame = doubleDifference 3 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_3_2_witness :
    (permuteCharge pairPerm_3_2.symm alpha = alpha ∨
      permuteCharge pairPerm_3_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_2.symm qCross = doubleDifference 3 2 ∨
      permuteCharge pairPerm_3_2.symm qSame = doubleDifference 3 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_3_4_witness :
    (permuteCharge pairPerm_3_4.symm alpha = alpha ∨
      permuteCharge pairPerm_3_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_4.symm qCross = doubleDifference 3 4 ∨
      permuteCharge pairPerm_3_4.symm qSame = doubleDifference 3 4) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_3_5_witness :
    (permuteCharge pairPerm_3_5.symm alpha = alpha ∨
      permuteCharge pairPerm_3_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_5.symm qCross = doubleDifference 3 5 ∨
      permuteCharge pairPerm_3_5.symm qSame = doubleDifference 3 5) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_4_0_witness :
    (permuteCharge pairPerm_4_0.symm alpha = alpha ∨
      permuteCharge pairPerm_4_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_0.symm qCross = doubleDifference 4 0 ∨
      permuteCharge pairPerm_4_0.symm qSame = doubleDifference 4 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_4_1_witness :
    (permuteCharge pairPerm_4_1.symm alpha = alpha ∨
      permuteCharge pairPerm_4_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_1.symm qCross = doubleDifference 4 1 ∨
      permuteCharge pairPerm_4_1.symm qSame = doubleDifference 4 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_4_2_witness :
    (permuteCharge pairPerm_4_2.symm alpha = alpha ∨
      permuteCharge pairPerm_4_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_2.symm qCross = doubleDifference 4 2 ∨
      permuteCharge pairPerm_4_2.symm qSame = doubleDifference 4 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_4_3_witness :
    (permuteCharge pairPerm_4_3.symm alpha = alpha ∨
      permuteCharge pairPerm_4_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_3.symm qCross = doubleDifference 4 3 ∨
      permuteCharge pairPerm_4_3.symm qSame = doubleDifference 4 3) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_4_5_witness :
    (permuteCharge pairPerm_4_5.symm alpha = alpha ∨
      permuteCharge pairPerm_4_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_5.symm qCross = doubleDifference 4 5 ∨
      permuteCharge pairPerm_4_5.symm qSame = doubleDifference 4 5) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_5_0_witness :
    (permuteCharge pairPerm_5_0.symm alpha = alpha ∨
      permuteCharge pairPerm_5_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_0.symm qCross = doubleDifference 5 0 ∨
      permuteCharge pairPerm_5_0.symm qSame = doubleDifference 5 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_5_1_witness :
    (permuteCharge pairPerm_5_1.symm alpha = alpha ∨
      permuteCharge pairPerm_5_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_1.symm qCross = doubleDifference 5 1 ∨
      permuteCharge pairPerm_5_1.symm qSame = doubleDifference 5 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_5_2_witness :
    (permuteCharge pairPerm_5_2.symm alpha = alpha ∨
      permuteCharge pairPerm_5_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_2.symm qCross = doubleDifference 5 2 ∨
      permuteCharge pairPerm_5_2.symm qSame = doubleDifference 5 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_5_3_witness :
    (permuteCharge pairPerm_5_3.symm alpha = alpha ∨
      permuteCharge pairPerm_5_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_3.symm qCross = doubleDifference 5 3 ∨
      permuteCharge pairPerm_5_3.symm qSame = doubleDifference 5 3) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_5_4_witness :
    (permuteCharge pairPerm_5_4.symm alpha = alpha ∨
      permuteCharge pairPerm_5_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_4.symm qCross = doubleDifference 5 4 ∨
      permuteCharge pairPerm_5_4.symm qSame = doubleDifference 5 4) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pair_permutation_witness (i j : Coord) (hij : i ≠ j) :
    ∃ π : Equiv.Perm Coord,
      (permuteCharge π.symm alpha = alpha ∨ permuteCharge π.symm alpha = -alpha) ∧
      (permuteCharge π.symm qCross = doubleDifference i j ∨
        permuteCharge π.symm qSame = doubleDifference i j) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_0_1, pairPerm_0_1_witness⟩
  · exact ⟨pairPerm_0_2, pairPerm_0_2_witness⟩
  · exact ⟨pairPerm_0_3, pairPerm_0_3_witness⟩
  · exact ⟨pairPerm_0_4, pairPerm_0_4_witness⟩
  · exact ⟨pairPerm_0_5, pairPerm_0_5_witness⟩
  · exact ⟨pairPerm_1_0, pairPerm_1_0_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_1_2, pairPerm_1_2_witness⟩
  · exact ⟨pairPerm_1_3, pairPerm_1_3_witness⟩
  · exact ⟨pairPerm_1_4, pairPerm_1_4_witness⟩
  · exact ⟨pairPerm_1_5, pairPerm_1_5_witness⟩
  · exact ⟨pairPerm_2_0, pairPerm_2_0_witness⟩
  · exact ⟨pairPerm_2_1, pairPerm_2_1_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_2_3, pairPerm_2_3_witness⟩
  · exact ⟨pairPerm_2_4, pairPerm_2_4_witness⟩
  · exact ⟨pairPerm_2_5, pairPerm_2_5_witness⟩
  · exact ⟨pairPerm_3_0, pairPerm_3_0_witness⟩
  · exact ⟨pairPerm_3_1, pairPerm_3_1_witness⟩
  · exact ⟨pairPerm_3_2, pairPerm_3_2_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_3_4, pairPerm_3_4_witness⟩
  · exact ⟨pairPerm_3_5, pairPerm_3_5_witness⟩
  · exact ⟨pairPerm_4_0, pairPerm_4_0_witness⟩
  · exact ⟨pairPerm_4_1, pairPerm_4_1_witness⟩
  · exact ⟨pairPerm_4_2, pairPerm_4_2_witness⟩
  · exact ⟨pairPerm_4_3, pairPerm_4_3_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_4_5, pairPerm_4_5_witness⟩
  · exact ⟨pairPerm_5_0, pairPerm_5_0_witness⟩
  · exact ⟨pairPerm_5_1, pairPerm_5_1_witness⟩
  · exact ⟨pairPerm_5_2, pairPerm_5_2_witness⟩
  · exact ⟨pairPerm_5_3, pairPerm_5_3_witness⟩
  · exact ⟨pairPerm_5_4, pairPerm_5_4_witness⟩
  · exact False.elim (hij rfl)

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Dichotomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem doubleDifference_zero_of_pair_products {H : CMatrix} (hH : IsHadamard H)
    (hp : PairProductsZero H) (ha : g H alpha ≠ 0) (i j : Coord) (hij : i ≠ j) :
    g H (doubleDifference i j) = 0 := by
  obtain ⟨π, hπα, hπq⟩ := pair_permutation_witness i j hij
  have hn : g (fun i j => H (π i) j) alpha ≠ 0 := by
    rw [g_row_permutation]
    rcases hπα with h | h
    · rw [h]
      exact ha
    · rw [h, g_neg hH]
      exact fun hzero => ha ((map_eq_zero (starRingEnd ℂ)).mp hzero)
  rcases hπq with h | h
  · have hz := (mul_eq_zero.mp (hp π).1).resolve_left hn
    rwa [g_row_permutation, h] at hz
  · have hz := (mul_eq_zero.mp (hp π).2).resolve_left hn
    rwa [g_row_permutation, h] at hz

theorem pair_products_row_permutation {H : CMatrix} (hp : PairProductsZero H)
    (π : Equiv.Perm Coord) : PairProductsZero (fun i j => H (π i) j) := by
  intro σ
  exact hp (σ.trans π)

/-- The manuscript's single-matrix dichotomy, conditional here only on the two
explicit pair-product identities. The finite certificate supplies them. -/
theorem dichotomy_of_pair_products {H : CMatrix} (hH : IsHadamard H)
    (hp : PairProductsZero H) : FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) := by
  classical
  by_cases hzero : FourierZero H
  · exact Or.inl hzero
  · right
    obtain ⟨π, hπ⟩ := not_forall.mp hzero
    let K : CMatrix := fun i j => H (π i) j
    have hK : IsHadamard K := hH.permutations π (Equiv.refl _)
    have hKp : PairProductsZero K := pair_products_row_permutation hp π
    have hKsquare : IsHadamard (fun i j => K i j ^ 2) :=
      square_isHadamard_of_doubleDifference_zero hK
        (doubleDifference_zero_of_pair_products hK hKp hπ)
    have h := hKsquare.permutations π.symm (Equiv.refl _)
    simpa only [K, Equiv.apply_symm_apply, Equiv.refl_apply] using h

theorem dichotomy_of_pair_certificates {H : CMatrix} (hH : IsHadamard H)
    (hcross : PairCertificateIdentity H qCross) (hsame : PairCertificateIdentity H qSame) :
    FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) := by
  apply dichotomy_of_pair_products hH
  intro π
  exact ⟨pair_product_zero_of_certificate hcross π, pair_product_zero_of_certificate hsame π⟩

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_FourierEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem FourierZero.permuted_charge {H : CMatrix} (h : FourierZero H)
    (π : Equiv.Perm Coord) : g H (permuteCharge π alpha) = 0 := by
  simpa only [g_row_permutation, Equiv.symm_symm] using h π.symm

/-- The structural deduction from the two exact pair identities. The final
endpoint instantiates these identities with their checked integer certificates. -/
theorem fourier_vanishing_of_pair_certificates {H : CMatrix} (hH : IsHadamard H)
    (hcross : PairCertificateIdentity H qCross) (hsame : PairCertificateIdentity H qSame)
    (hTao : ¬Equivalent H tao) (π : Equiv.Perm Coord) :
    g H (permuteCharge π alpha) = 0 := by
  rcases dichotomy_of_pair_certificates hH hcross hsame with hz | hs
  · exact hz.permuted_charge π
  · exact (hTao (hadamard_square_equivalent_tao hH hs)).elim

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Terms
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

private theorem charge0_0 :
    (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (0 : Fin 2)) = pairW := by decide +kernel

private theorem charge0_1 :
    (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (1 : Fin 2)) = -pairW := by decide +kernel

theorem termPolynomial0 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term0 = (3 : ℂ) * ((g H pairW) * (conj (g H pairW))) := by
  have hc : (term0.coefficient : ℂ) = (3 : ℂ) := by norm_num [term0]
  change (term0.coefficient : ℂ) * (∏ j : Fin 2, g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (0 : Fin 2)) * (g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (1 : Fin 2)) * 1)) = _
  rw [charge0_0, charge0_1]
  simp only [g_neg hH]
  ring

private theorem charge1_0 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge1_1 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 0) := by decide +kernel

private theorem charge1_2 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial1 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term1 = (-6 : ℂ) * ((g H pairW) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term1.coefficient : ℂ) = (-6 : ℂ) := by norm_num [term1]
  change (term1.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-6 : ℂ) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge1_0, charge1_1, charge1_2]
  simp only [g_neg hH]
  ring

private theorem charge2_0 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge2_1 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 1) := by decide +kernel

private theorem charge2_2 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial2 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term2 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term2.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term2]
  change (term2.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge2_0, charge2_1, charge2_2]
  simp only [g_neg hH]
  ring

private theorem charge3_0 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge3_1 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 2) := by decide +kernel

private theorem charge3_2 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial3 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term3 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term3.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term3]
  change (term3.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge3_0, charge3_1, charge3_2]
  simp only [g_neg hH]
  ring

private theorem charge4_0 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge4_1 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 3) := by decide +kernel

private theorem charge4_2 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial4 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term4 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term4.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term4]
  change (term4.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge4_0, charge4_1, charge4_2]
  simp only [g_neg hH]
  ring

private theorem charge5_0 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 0) := by decide +kernel

private theorem charge5_1 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 0) := by decide +kernel

private theorem charge5_2 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial5 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term5 = (-6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H pairW))) := by
  have hc : (term5.coefficient : ℂ) = (-6 : ℂ) := by norm_num [term5]
  change (term5.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-6 : ℂ) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge5_0, charge5_1, charge5_2]
  simp only [g_neg hH]
  ring

private theorem charge6_0 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge6_1 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge6_2 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge6_3 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial6 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term6 = (12 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term6.coefficient : ℂ) = (12 : ℂ) := by norm_num [term6]
  change (term6.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (12 : ℂ) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge6_0, charge6_1, charge6_2, charge6_3]
  simp only [g_neg hH]
  ring

private theorem charge7_0 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge7_1 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge7_2 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge7_3 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial7 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term7 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term7.coefficient : ℂ) = (6 : ℂ) := by norm_num [term7]
  change (term7.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge7_0, charge7_1, charge7_2, charge7_3]
  simp only [g_neg hH]
  ring

private theorem charge8_0 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge8_1 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge8_2 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge8_3 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial8 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term8 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term8.coefficient : ℂ) = (6 : ℂ) := by norm_num [term8]
  change (term8.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge8_0, charge8_1, charge8_2, charge8_3]
  simp only [g_neg hH]
  ring

private theorem charge9_0 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge9_1 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge9_2 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge9_3 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial9 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term9 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term9.coefficient : ℂ) = (6 : ℂ) := by norm_num [term9]
  change (term9.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge9_0, charge9_1, charge9_2, charge9_3]
  simp only [g_neg hH]
  ring

private theorem charge10_0 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 1) := by decide +kernel

private theorem charge10_1 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 1) := by decide +kernel

private theorem charge10_2 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial10 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term10 = (-3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H pairW))) := by
  have hc : (term10.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term10]
  change (term10.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge10_0, charge10_1, charge10_2]
  simp only [g_neg hH]
  ring

private theorem charge11_0 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge11_1 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge11_2 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge11_3 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial11 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term11 = (6 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term11.coefficient : ℂ) = (6 : ℂ) := by norm_num [term11]
  change (term11.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge11_0, charge11_1, charge11_2, charge11_3]
  simp only [g_neg hH]
  ring

private theorem charge12_0 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge12_1 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge12_2 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge12_3 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial12 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term12 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term12.coefficient : ℂ) = (3 : ℂ) := by norm_num [term12]
  change (term12.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge12_0, charge12_1, charge12_2, charge12_3]
  simp only [g_neg hH]
  ring

private theorem charge13_0 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge13_1 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge13_2 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge13_3 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial13 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term13 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term13.coefficient : ℂ) = (3 : ℂ) := by norm_num [term13]
  change (term13.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge13_0, charge13_1, charge13_2, charge13_3]
  simp only [g_neg hH]
  ring

private theorem charge14_0 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge14_1 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge14_2 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge14_3 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial14 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term14 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term14.coefficient : ℂ) = (3 : ℂ) := by norm_num [term14]
  change (term14.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge14_0, charge14_1, charge14_2, charge14_3]
  simp only [g_neg hH]
  ring

private theorem charge15_0 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 2) := by decide +kernel

private theorem charge15_1 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 2) := by decide +kernel

private theorem charge15_2 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial15 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term15 = (-3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H pairW))) := by
  have hc : (term15.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term15]
  change (term15.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge15_0, charge15_1, charge15_2]
  simp only [g_neg hH]
  ring

private theorem charge16_0 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge16_1 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge16_2 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge16_3 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial16 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term16 = (6 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term16.coefficient : ℂ) = (6 : ℂ) := by norm_num [term16]
  change (term16.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge16_0, charge16_1, charge16_2, charge16_3]
  simp only [g_neg hH]
  ring

private theorem charge17_0 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge17_1 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge17_2 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge17_3 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial17 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term17 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term17.coefficient : ℂ) = (3 : ℂ) := by norm_num [term17]
  change (term17.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge17_0, charge17_1, charge17_2, charge17_3]
  simp only [g_neg hH]
  ring

private theorem charge18_0 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge18_1 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge18_2 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge18_3 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial18 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term18 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term18.coefficient : ℂ) = (3 : ℂ) := by norm_num [term18]
  change (term18.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge18_0, charge18_1, charge18_2, charge18_3]
  simp only [g_neg hH]
  ring

private theorem charge19_0 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge19_1 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge19_2 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge19_3 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial19 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term19 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term19.coefficient : ℂ) = (3 : ℂ) := by norm_num [term19]
  change (term19.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge19_0, charge19_1, charge19_2, charge19_3]
  simp only [g_neg hH]
  ring

private theorem charge20_0 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 3) := by decide +kernel

private theorem charge20_1 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 3) := by decide +kernel

private theorem charge20_2 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial20 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term20 = (-3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H pairW))) := by
  have hc : (term20.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term20]
  change (term20.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge20_0, charge20_1, charge20_2]
  simp only [g_neg hH]
  ring

private theorem charge21_0 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge21_1 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge21_2 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge21_3 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial21 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term21 = (6 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term21.coefficient : ℂ) = (6 : ℂ) := by norm_num [term21]
  change (term21.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge21_0, charge21_1, charge21_2, charge21_3]
  simp only [g_neg hH]
  ring

private theorem charge22_0 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge22_1 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge22_2 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge22_3 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial22 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term22 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term22.coefficient : ℂ) = (3 : ℂ) := by norm_num [term22]
  change (term22.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge22_0, charge22_1, charge22_2, charge22_3]
  simp only [g_neg hH]
  ring

private theorem charge23_0 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge23_1 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge23_2 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge23_3 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial23 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term23 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term23.coefficient : ℂ) = (3 : ℂ) := by norm_num [term23]
  change (term23.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge23_0, charge23_1, charge23_2, charge23_3]
  simp only [g_neg hH]
  ring

private theorem charge24_0 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge24_1 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge24_2 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge24_3 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial24 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term24 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term24.coefficient : ℂ) = (3 : ℂ) := by norm_num [term24]
  change (term24.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge24_0, charge24_1, charge24_2, charge24_3]
  simp only [g_neg hH]
  ring

private theorem charge26_0 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = alpha := by decide +kernel

private theorem charge26_1 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = qSame := by decide +kernel

private theorem charge26_2 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -alpha := by decide +kernel

private theorem charge26_3 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -qSame := by decide +kernel

theorem termPolynomial26 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term26 = (1 : ℂ) * ((g H alpha) * (g H qSame) * (conj (g H alpha)) * (conj (g H qSame))) := by
  have hc : (term26.coefficient : ℂ) = (1 : ℂ) := by norm_num [term26]
  change (term26.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (1 : ℂ) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge26_0, charge26_1, charge26_2, charge26_3]
  simp only [g_neg hH]
  ring

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Grid
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

theorem pairSummand_sum (H : CMatrix) : (∑ r, pairSummand H r) = pairL H := by
  simp [pairSummand, pairL, pairCoefficient, Fin.sum_univ_succ]

private theorem grid0 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 0) = 3 * (pairSummand H 0 * conj (pairSummand H 0)) := by
  change termPolynomial H term0 = _
  rw [termPolynomial0 hH]
  simp [pairSummand, map_neg]

private theorem grid1 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 1) = 3 * (pairSummand H 0 * conj (pairSummand H 1)) := by
  change termPolynomial H term1 = _
  rw [termPolynomial1 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid2 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 2) = 3 * (pairSummand H 0 * conj (pairSummand H 2)) := by
  change termPolynomial H term2 = _
  rw [termPolynomial2 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid3 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 3) = 3 * (pairSummand H 0 * conj (pairSummand H 3)) := by
  change termPolynomial H term3 = _
  rw [termPolynomial3 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid4 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 4) = 3 * (pairSummand H 0 * conj (pairSummand H 4)) := by
  change termPolynomial H term4 = _
  rw [termPolynomial4 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid5 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 0) = 3 * (pairSummand H 1 * conj (pairSummand H 0)) := by
  change termPolynomial H term5 = _
  rw [termPolynomial5 hH]
  simp [pairSummand, map_neg]
  ring

private theorem grid6 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 1) = 3 * (pairSummand H 1 * conj (pairSummand H 1)) := by
  change termPolynomial H term6 = _
  rw [termPolynomial6 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid7 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 2) = 3 * (pairSummand H 1 * conj (pairSummand H 2)) := by
  change termPolynomial H term7 = _
  rw [termPolynomial7 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid8 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 3) = 3 * (pairSummand H 1 * conj (pairSummand H 3)) := by
  change termPolynomial H term8 = _
  rw [termPolynomial8 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid9 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 4) = 3 * (pairSummand H 1 * conj (pairSummand H 4)) := by
  change termPolynomial H term9 = _
  rw [termPolynomial9 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid10 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 0) = 3 * (pairSummand H 2 * conj (pairSummand H 0)) := by
  change termPolynomial H term10 = _
  rw [termPolynomial10 hH]
  simp [pairSummand, map_neg]

private theorem grid11 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 1) = 3 * (pairSummand H 2 * conj (pairSummand H 1)) := by
  change termPolynomial H term11 = _
  rw [termPolynomial11 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid12 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 2) = 3 * (pairSummand H 2 * conj (pairSummand H 2)) := by
  change termPolynomial H term12 = _
  rw [termPolynomial12 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid13 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 3) = 3 * (pairSummand H 2 * conj (pairSummand H 3)) := by
  change termPolynomial H term13 = _
  rw [termPolynomial13 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid14 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 4) = 3 * (pairSummand H 2 * conj (pairSummand H 4)) := by
  change termPolynomial H term14 = _
  rw [termPolynomial14 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid15 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 0) = 3 * (pairSummand H 3 * conj (pairSummand H 0)) := by
  change termPolynomial H term15 = _
  rw [termPolynomial15 hH]
  simp [pairSummand, map_neg]

private theorem grid16 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 1) = 3 * (pairSummand H 3 * conj (pairSummand H 1)) := by
  change termPolynomial H term16 = _
  rw [termPolynomial16 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid17 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 2) = 3 * (pairSummand H 3 * conj (pairSummand H 2)) := by
  change termPolynomial H term17 = _
  rw [termPolynomial17 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid18 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 3) = 3 * (pairSummand H 3 * conj (pairSummand H 3)) := by
  change termPolynomial H term18 = _
  rw [termPolynomial18 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid19 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 4) = 3 * (pairSummand H 3 * conj (pairSummand H 4)) := by
  change termPolynomial H term19 = _
  rw [termPolynomial19 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid20 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 0) = 3 * (pairSummand H 4 * conj (pairSummand H 0)) := by
  change termPolynomial H term20 = _
  rw [termPolynomial20 hH]
  simp [pairSummand, map_neg]

private theorem grid21 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 1) = 3 * (pairSummand H 4 * conj (pairSummand H 1)) := by
  change termPolynomial H term21 = _
  rw [termPolynomial21 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid22 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 2) = 3 * (pairSummand H 4 * conj (pairSummand H 2)) := by
  change termPolynomial H term22 = _
  rw [termPolynomial22 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid23 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 3) = 3 * (pairSummand H 4 * conj (pairSummand H 3)) := by
  change termPolynomial H term23 = _
  rw [termPolynomial23 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid24 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 4) = 3 * (pairSummand H 4 * conj (pairSummand H 4)) := by
  change termPolynomial H term24 = _
  rw [termPolynomial24 hH]
  simp [pairSummand, map_mul]
  ring

theorem termGrid_polynomial {H : CMatrix} (hH : IsHadamard H) (r s : Fin 5) :
    termPolynomial H (termGrid r s) = 3 * (pairSummand H r * conj (pairSummand H s)) := by
  fin_cases r
  · fin_cases s
    · exact grid0 hH
    · exact grid1 hH
    · exact grid2 hH
    · exact grid3 hH
    · exact grid4 hH
  · fin_cases s
    · exact grid5 hH
    · exact grid6 hH
    · exact grid7 hH
    · exact grid8 hH
    · exact grid9 hH
  · fin_cases s
    · exact grid10 hH
    · exact grid11 hH
    · exact grid12 hH
    · exact grid13 hH
    · exact grid14 hH
  · fin_cases s
    · exact grid15 hH
    · exact grid16 hH
    · exact grid17 hH
    · exact grid18 hH
    · exact grid19 hH
  · fin_cases s
    · exact grid20 hH
    · exact grid21 hH
    · exact grid22 hH
    · exact grid23 hH
    · exact grid24 hH

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

theorem sum_grid_polynomial (x : Fin 5 → ℂ) :
    (∑ r, ∑ s, 3 * (x r * conj (x s))) = 3 * ((∑ r, x r) * conj (∑ s, x s)) := by
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem termGrid_at0 : termGrid 0 0 = term0 := rfl
private theorem termGrid_at1 : termGrid 0 1 = term1 := rfl
private theorem termGrid_at2 : termGrid 0 2 = term2 := rfl
private theorem termGrid_at3 : termGrid 0 3 = term3 := rfl
private theorem termGrid_at4 : termGrid 0 4 = term4 := rfl
private theorem termGrid_at5 : termGrid 1 0 = term5 := rfl
private theorem termGrid_at6 : termGrid 1 1 = term6 := rfl
private theorem termGrid_at7 : termGrid 1 2 = term7 := rfl
private theorem termGrid_at8 : termGrid 1 3 = term8 := rfl
private theorem termGrid_at9 : termGrid 1 4 = term9 := rfl
private theorem termGrid_at10 : termGrid 2 0 = term10 := rfl
private theorem termGrid_at11 : termGrid 2 1 = term11 := rfl
private theorem termGrid_at12 : termGrid 2 2 = term12 := rfl
private theorem termGrid_at13 : termGrid 2 3 = term13 := rfl
private theorem termGrid_at14 : termGrid 2 4 = term14 := rfl
private theorem termGrid_at15 : termGrid 3 0 = term15 := rfl
private theorem termGrid_at16 : termGrid 3 1 = term16 := rfl
private theorem termGrid_at17 : termGrid 3 2 = term17 := rfl
private theorem termGrid_at18 : termGrid 3 3 = term18 := rfl
private theorem termGrid_at19 : termGrid 3 4 = term19 := rfl
private theorem termGrid_at20 : termGrid 4 0 = term20 := rfl
private theorem termGrid_at21 : termGrid 4 1 = term21 := rfl
private theorem termGrid_at22 : termGrid 4 2 = term22 := rfl
private theorem termGrid_at23 : termGrid 4 3 = term23 := rfl
private theorem termGrid_at24 : termGrid 4 4 = term24 := rfl

private theorem terms1_at0 : terms1 0 = term0 := rfl
private theorem terms1_at1 : terms1 1 = term1 := rfl
private theorem terms1_at2 : terms1 2 = term2 := rfl
private theorem terms1_at3 : terms1 3 = term3 := rfl
private theorem terms1_at4 : terms1 4 = term4 := rfl
private theorem terms1_at5 : terms1 5 = term5 := rfl
private theorem terms1_at6 : terms1 6 = term6 := rfl
private theorem terms1_at7 : terms1 7 = term7 := rfl
private theorem terms1_at8 : terms1 8 = term8 := rfl
private theorem terms1_at9 : terms1 9 = term9 := rfl
private theorem terms1_at10 : terms1 10 = term10 := rfl
private theorem terms1_at11 : terms1 11 = term11 := rfl
private theorem terms1_at12 : terms1 12 = term12 := rfl
private theorem terms1_at13 : terms1 13 = term13 := rfl
private theorem terms1_at14 : terms1 14 = term14 := rfl
private theorem terms1_at15 : terms1 15 = term15 := rfl
private theorem terms1_at16 : terms1 16 = term16 := rfl
private theorem terms1_at17 : terms1 17 = term17 := rfl
private theorem terms1_at18 : terms1 18 = term18 := rfl
private theorem terms1_at19 : terms1 19 = term19 := rfl
private theorem terms1_at20 : terms1 20 = term20 := rfl
private theorem terms1_at21 : terms1 21 = term21 := rfl
private theorem terms1_at22 : terms1 22 = term22 := rfl
private theorem terms1_at23 : terms1 23 = term23 := rfl
private theorem terms1_at24 : terms1 24 = term24 := rfl
private theorem terms1_at25 : terms1 25 = term26 := rfl
theorem sum_terms1 (F : Term → ℂ) :
    (∑ i : Fin 26, F (terms1 i)) = (∑ r : Fin 5, ∑ s : Fin 5, F (termGrid r s)) + F term26 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms1 0) + (F (terms1 1) + (F (terms1 2) + (F (terms1 3) + (F (terms1 4) + (F (terms1 5) + (F (terms1 6) + (F (terms1 7) + (F (terms1 8) + (F (terms1 9) + (F (terms1 10) + (F (terms1 11) + (F (terms1 12) + (F (terms1 13) + (F (terms1 14) + (F (terms1 15) + (F (terms1 16) + (F (terms1 17) + (F (terms1 18) + (F (terms1 19) + (F (terms1 20) + (F (terms1 21) + (F (terms1 22) + (F (terms1 23) + (F (terms1 24) + (F (terms1 25) + 0)))))))))))))))))))))))))) = ((F (termGrid 0 0) + (F (termGrid 0 1) + (F (termGrid 0 2) + (F (termGrid 0 3) + (F (termGrid 0 4) + 0))))) + ((F (termGrid 1 0) + (F (termGrid 1 1) + (F (termGrid 1 2) + (F (termGrid 1 3) + (F (termGrid 1 4) + 0))))) + ((F (termGrid 2 0) + (F (termGrid 2 1) + (F (termGrid 2 2) + (F (termGrid 2 3) + (F (termGrid 2 4) + 0))))) + ((F (termGrid 3 0) + (F (termGrid 3 1) + (F (termGrid 3 2) + (F (termGrid 3 3) + (F (termGrid 3 4) + 0))))) + ((F (termGrid 4 0) + (F (termGrid 4 1) + (F (termGrid 4 2) + (F (termGrid 4 3) + (F (termGrid 4 4) + 0))))) + 0))))) + F term26
  simp only [terms1_at0, terms1_at1, terms1_at2, terms1_at3, terms1_at4, terms1_at5, terms1_at6, terms1_at7, terms1_at8, terms1_at9, terms1_at10, terms1_at11, terms1_at12, terms1_at13, terms1_at14, terms1_at15, terms1_at16, terms1_at17, terms1_at18, terms1_at19, terms1_at20, terms1_at21, terms1_at22, terms1_at23, terms1_at24, terms1_at25, termGrid_at0, termGrid_at1, termGrid_at2, termGrid_at3, termGrid_at4, termGrid_at5, termGrid_at6, termGrid_at7, termGrid_at8, termGrid_at9, termGrid_at10, termGrid_at11, termGrid_at12, termGrid_at13, termGrid_at14, termGrid_at15, termGrid_at16, termGrid_at17, termGrid_at18, termGrid_at19, termGrid_at20, termGrid_at21, termGrid_at22, termGrid_at23, termGrid_at24, add_zero, add_assoc]

theorem pair_polynomial1 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, termPolynomial H (terms1 i)) =
      3 * (pairL H * conj (pairL H)) +
        (g H alpha * g H qSame) * conj (g H alpha * g H qSame) := by
  rw [sum_terms1]
  simp_rw [termGrid_polynomial hH]
  rw [sum_grid_polynomial, pairSummand_sum, termPolynomial26 hH]
  simp only [map_mul, one_mul]
  ring

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairInterpretation
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem pairAverage_add (H : CMatrix) (F G : CMatrix → ℝ) :
    pairAverage H (fun K => F K + G K) = pairAverage H F + pairAverage H G := by
  have h (π : Equiv.Perm Coord) :
      ((F (fun i j => H (π i) j) + G (fun i j => H (π i) j)) +
        (F (fun i j => H j (π i)) + G (fun i j => H j (π i)))) / 2 =
      (F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2 +
        (G (fun i j => H (π i) j) + G (fun i j => H j (π i))) / 2 := by ring
  simp only [pairAverage, h, average_add]

theorem pairAverage_mul (H : CMatrix) (c : ℝ) (F : CMatrix → ℝ) :
    pairAverage H (fun K => c * F K) = c * pairAverage H F := by
  unfold pairAverage
  have h (π : Equiv.Perm Coord) :
      (c * F (fun i j => H (π i) j) + c * F (fun i j => H j (π i))) / 2 =
      c * ((F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2) := by ring
  simp_rw [h]
  exact average_mul c _

theorem pairAverage_sum {ι : Type*} [Fintype ι] (H : CMatrix) (F : ι → CMatrix → ℝ) :
    pairAverage H (fun K => ∑ i, F i K) = ∑ i, pairAverage H (F i) := by
  simp only [pairAverage, ← Finset.sum_add_distrib, div_eq_mul_inv,
    Finset.sum_mul, average_sum]

theorem pairAverage_congr_hadamard {H : CMatrix} (hH : IsHadamard H)
    {F G : CMatrix → ℝ} (h : ∀ K, IsHadamard K → F K = G K) :
    pairAverage H F = pairAverage H G := by
  apply average_congr
  intro π
  have h₁ : IsHadamard (fun i j => H (π i) j) := by
    simpa only [Equiv.refl_apply] using hH.permutations π (Equiv.refl Coord)
  have h₂ : IsHadamard (fun i j => H j (π i)) := by
    simpa only [Equiv.refl_apply, Matrix.transpose_apply] using
      hH.transpose.permutations π (Equiv.refl Coord)
  rw [h _ h₁, h _ h₂]

namespace Certificate.PairTargetSemantics

theorem termPolynomial_re (H : CMatrix) (t : Term) :
    (termPolynomial H t).re = (t.coefficient : ℝ) * (∏ j, g H (fun i => t.charges i j)).re := by
  simp [termPolynomial, Complex.mul_re]

theorem pair_real_polynomial1 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, ((terms1 i).coefficient : ℝ) *
      (∏ j, g H (fun k => (terms1 i).charges k j)).re) =
      3 * Complex.normSq (pairL H) + Complex.normSq (g H alpha * g H qSame) := by
  have h := congrArg Complex.re (pair_polynomial1 hH)
  rw [Complex.mul_conj, Complex.mul_conj] at h
  simpa only [Complex.re_sum, termPolynomial_re, Complex.add_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

theorem expanded_identity1 {H : CMatrix} (hH : IsHadamard H) :
    expanded1 H = 3 * pairAverage H (fun K => Complex.normSq (pairL K)) +
      pairAverage H (fun K => Complex.normSq (g K alpha * g K qSame)) := by
  calc
    _ = pairAverage H (fun K => ∑ i : Fin 26, ((terms1 i).coefficient : ℝ) *
        (∏ j, g K (fun k => (terms1 i).charges k j)).re) := by
      simp only [pairAverage_sum, pairAverage_mul, expanded1, weightedAverage]
    _ = pairAverage H (fun K => 3 * Complex.normSq (pairL K) +
        Complex.normSq (g K alpha * g K qSame)) :=
      pairAverage_congr_hadamard hH (fun _ hK => pair_real_polynomial1 hK)
    _ = _ := by rw [pairAverage_add, pairAverage_mul]

end Certificate.PairTargetSemantics
end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck254 : pairMerged254 = Integer.Sparse.merge (Integer.Sparse.scale (-302313060) (rows 1)) (Integer.Sparse.scale (207408600) (rows 2)) := by decide +kernel

theorem pairMergedZero254 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged254 x = 0 := by
  rw [pairMergeCheck254, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck255 : pairMerged255 = Integer.Sparse.merge (Integer.Sparse.scale (-55755000) (rows 0)) pairMerged254 := by decide +kernel

theorem pairMergedZero255 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged255 x = 0 := by
  rw [pairMergeCheck255, Integer.Sparse.eval_merge]
  rw [pairMergedZero254 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck256 : pairMerged256 = Integer.Sparse.merge (Integer.Sparse.scale (-45274194) (rows 4)) (Integer.Sparse.scale (24898104) (rows 5)) := by decide +kernel

theorem pairMergedZero256 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged256 x = 0 := by
  rw [pairMergeCheck256, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck257 : pairMerged257 = Integer.Sparse.merge (Integer.Sparse.scale (27823824) (rows 3)) pairMerged256 := by decide +kernel

theorem pairMergedZero257 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged257 x = 0 := by
  rw [pairMergeCheck257, Integer.Sparse.eval_merge]
  rw [pairMergedZero256 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck258 : pairMerged258 = Integer.Sparse.merge pairMerged255 pairMerged257 := by decide +kernel

theorem pairMergedZero258 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged258 x = 0 := by
  rw [pairMergeCheck258, Integer.Sparse.eval_merge]
  rw [pairMergedZero255 x h, pairMergedZero257 x h]
  simp only [add_zero]

theorem pairMergeCheck259 : pairMerged259 = Integer.Sparse.merge (Integer.Sparse.scale (-42819840) (rows 7)) (Integer.Sparse.scale (-2349648) (rows 8)) := by decide +kernel

theorem pairMergedZero259 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged259 x = 0 := by
  rw [pairMergeCheck259, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck260 : pairMerged260 = Integer.Sparse.merge (Integer.Sparse.scale (61467336) (rows 6)) pairMerged259 := by decide +kernel

theorem pairMergedZero260 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged260 x = 0 := by
  rw [pairMergeCheck260, Integer.Sparse.eval_merge]
  rw [pairMergedZero259 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck261 : pairMerged261 = Integer.Sparse.merge (Integer.Sparse.scale (4220748) (rows 9)) (Integer.Sparse.scale (1111320) (rows 10)) := by decide +kernel

theorem pairMergedZero261 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged261 x = 0 := by
  rw [pairMergeCheck261, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck262 : pairMerged262 = Integer.Sparse.merge (Integer.Sparse.scale (-2268000) (rows 11)) (Integer.Sparse.scale (-11113200) (rows 12)) := by decide +kernel

theorem pairMergedZero262 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged262 x = 0 := by
  rw [pairMergeCheck262, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck263 : pairMerged263 = Integer.Sparse.merge pairMerged261 pairMerged262 := by decide +kernel

theorem pairMergedZero263 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged263 x = 0 := by
  rw [pairMergeCheck263, Integer.Sparse.eval_merge]
  rw [pairMergedZero261 x h, pairMergedZero262 x h]
  simp only [add_zero]

theorem pairMergeCheck264 : pairMerged264 = Integer.Sparse.merge pairMerged260 pairMerged263 := by decide +kernel

theorem pairMergedZero264 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged264 x = 0 := by
  rw [pairMergeCheck264, Integer.Sparse.eval_merge]
  rw [pairMergedZero260 x h, pairMergedZero263 x h]
  simp only [add_zero]

theorem pairMergeCheck265 : pairMerged265 = Integer.Sparse.merge pairMerged258 pairMerged264 := by decide +kernel

theorem pairMergedZero265 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged265 x = 0 := by
  rw [pairMergeCheck265, Integer.Sparse.eval_merge]
  rw [pairMergedZero258 x h, pairMergedZero264 x h]
  simp only [add_zero]

theorem pairMergeCheck266 : pairMerged266 = Integer.Sparse.merge (Integer.Sparse.scale (6393492) (rows 14)) (Integer.Sparse.scale (272160) (rows 15)) := by decide +kernel

theorem pairMergedZero266 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged266 x = 0 := by
  rw [pairMergeCheck266, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck267 : pairMerged267 = Integer.Sparse.merge (Integer.Sparse.scale (-555660) (rows 13)) pairMerged266 := by decide +kernel

theorem pairMergedZero267 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged267 x = 0 := by
  rw [pairMergeCheck267, Integer.Sparse.eval_merge]
  rw [pairMergedZero266 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck268 : pairMerged268 = Integer.Sparse.merge (Integer.Sparse.scale (6483834) (rows 16)) (Integer.Sparse.scale (-1272348) (rows 17)) := by decide +kernel

theorem pairMergedZero268 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged268 x = 0 := by
  rw [pairMergeCheck268, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck269 : pairMerged269 = Integer.Sparse.merge (Integer.Sparse.scale (-1124928) (rows 18)) (Integer.Sparse.scale (-24284610) (rows 19)) := by decide +kernel

theorem pairMergedZero269 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged269 x = 0 := by
  rw [pairMergeCheck269, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck270 : pairMerged270 = Integer.Sparse.merge pairMerged268 pairMerged269 := by decide +kernel

theorem pairMergedZero270 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged270 x = 0 := by
  rw [pairMergeCheck270, Integer.Sparse.eval_merge]
  rw [pairMergedZero268 x h, pairMergedZero269 x h]
  simp only [add_zero]

theorem pairMergeCheck271 : pairMerged271 = Integer.Sparse.merge pairMerged267 pairMerged270 := by decide +kernel

theorem pairMergedZero271 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged271 x = 0 := by
  rw [pairMergeCheck271, Integer.Sparse.eval_merge]
  rw [pairMergedZero267 x h, pairMergedZero270 x h]
  simp only [add_zero]

theorem pairMergeCheck272 : pairMerged272 = Integer.Sparse.merge (Integer.Sparse.scale (5928552) (rows 21)) (Integer.Sparse.scale (3525984) (rows 22)) := by decide +kernel

theorem pairMergedZero272 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged272 x = 0 := by
  rw [pairMergeCheck272, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck273 : pairMerged273 = Integer.Sparse.merge (Integer.Sparse.scale (-18510660) (rows 20)) pairMerged272 := by decide +kernel

theorem pairMergedZero273 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged273 x = 0 := by
  rw [pairMergeCheck273, Integer.Sparse.eval_merge]
  rw [pairMergedZero272 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck274 : pairMerged274 = Integer.Sparse.merge (Integer.Sparse.scale (-2667168) (rows 23)) (Integer.Sparse.scale (-23879772) (rows 24)) := by decide +kernel

theorem pairMergedZero274 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged274 x = 0 := by
  rw [pairMergeCheck274, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck275 : pairMerged275 = Integer.Sparse.merge (Integer.Sparse.scale (5100732) (rows 25)) (Integer.Sparse.scale (-569268) (rows 26)) := by decide +kernel

theorem pairMergedZero275 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged275 x = 0 := by
  rw [pairMergeCheck275, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck276 : pairMerged276 = Integer.Sparse.merge pairMerged274 pairMerged275 := by decide +kernel

theorem pairMergedZero276 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged276 x = 0 := by
  rw [pairMergeCheck276, Integer.Sparse.eval_merge]
  rw [pairMergedZero274 x h, pairMergedZero275 x h]
  simp only [add_zero]

theorem pairMergeCheck277 : pairMerged277 = Integer.Sparse.merge pairMerged273 pairMerged276 := by decide +kernel

theorem pairMergedZero277 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged277 x = 0 := by
  rw [pairMergeCheck277, Integer.Sparse.eval_merge]
  rw [pairMergedZero273 x h, pairMergedZero276 x h]
  simp only [add_zero]

theorem pairMergeCheck278 : pairMerged278 = Integer.Sparse.merge pairMerged271 pairMerged277 := by decide +kernel

theorem pairMergedZero278 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged278 x = 0 := by
  rw [pairMergeCheck278, Integer.Sparse.eval_merge]
  rw [pairMergedZero271 x h, pairMergedZero277 x h]
  simp only [add_zero]

theorem pairMergeCheck279 : pairMerged279 = Integer.Sparse.merge pairMerged265 pairMerged278 := by decide +kernel

theorem pairMergedZero279 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged279 x = 0 := by
  rw [pairMergeCheck279, Integer.Sparse.eval_merge]
  rw [pairMergedZero265 x h, pairMergedZero278 x h]
  simp only [add_zero]

theorem pairMergeCheck280 : pairMerged280 = Integer.Sparse.merge (Integer.Sparse.scale (1315440) (rows 28)) (Integer.Sparse.scale (-5406912) (rows 29)) := by decide +kernel

theorem pairMergedZero280 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged280 x = 0 := by
  rw [pairMergeCheck280, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck281 : pairMerged281 = Integer.Sparse.merge (Integer.Sparse.scale (-8544690) (rows 27)) pairMerged280 := by decide +kernel

theorem pairMergedZero281 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged281 x = 0 := by
  rw [pairMergeCheck281, Integer.Sparse.eval_merge]
  rw [pairMergedZero280 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck282 : pairMerged282 = Integer.Sparse.merge (Integer.Sparse.scale (1625022) (rows 31)) (Integer.Sparse.scale (-8954064) (rows 32)) := by decide +kernel

theorem pairMergedZero282 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged282 x = 0 := by
  rw [pairMergeCheck282, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck283 : pairMerged283 = Integer.Sparse.merge (Integer.Sparse.scale (2703456) (rows 30)) pairMerged282 := by decide +kernel

theorem pairMergedZero283 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged283 x = 0 := by
  rw [pairMergeCheck283, Integer.Sparse.eval_merge]
  rw [pairMergedZero282 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck284 : pairMerged284 = Integer.Sparse.merge pairMerged281 pairMerged283 := by decide +kernel

theorem pairMergedZero284 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged284 x = 0 := by
  rw [pairMergeCheck284, Integer.Sparse.eval_merge]
  rw [pairMergedZero281 x h, pairMergedZero283 x h]
  simp only [add_zero]

theorem pairMergeCheck285 : pairMerged285 = Integer.Sparse.merge (Integer.Sparse.scale (-1298430) (rows 34)) (Integer.Sparse.scale (3027780) (rows 36)) := by decide +kernel

theorem pairMergedZero285 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged285 x = 0 := by
  rw [pairMergeCheck285, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck286 : pairMerged286 = Integer.Sparse.merge (Integer.Sparse.scale (1429974) (rows 33)) pairMerged285 := by decide +kernel

theorem pairMergedZero286 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged286 x = 0 := by
  rw [pairMergeCheck286, Integer.Sparse.eval_merge]
  rw [pairMergedZero285 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck287 : pairMerged287 = Integer.Sparse.merge (Integer.Sparse.scale (-260820) (rows 37)) (Integer.Sparse.scale (15354360) (rows 39)) := by decide +kernel

theorem pairMergedZero287 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged287 x = 0 := by
  rw [pairMergeCheck287, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck288 : pairMerged288 = Integer.Sparse.merge (Integer.Sparse.scale (2140992) (rows 40)) (Integer.Sparse.scale (-1007559) (rows 41)) := by decide +kernel

theorem pairMergedZero288 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged288 x = 0 := by
  rw [pairMergeCheck288, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck289 : pairMerged289 = Integer.Sparse.merge pairMerged287 pairMerged288 := by decide +kernel

theorem pairMergedZero289 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged289 x = 0 := by
  rw [pairMergeCheck289, Integer.Sparse.eval_merge]
  rw [pairMergedZero287 x h, pairMergedZero288 x h]
  simp only [add_zero]

theorem pairMergeCheck290 : pairMerged290 = Integer.Sparse.merge pairMerged286 pairMerged289 := by decide +kernel

theorem pairMergedZero290 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged290 x = 0 := by
  rw [pairMergeCheck290, Integer.Sparse.eval_merge]
  rw [pairMergedZero286 x h, pairMergedZero289 x h]
  simp only [add_zero]

theorem pairMergeCheck291 : pairMerged291 = Integer.Sparse.merge pairMerged284 pairMerged290 := by decide +kernel

theorem pairMergedZero291 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged291 x = 0 := by
  rw [pairMergeCheck291, Integer.Sparse.eval_merge]
  rw [pairMergedZero284 x h, pairMergedZero290 x h]
  simp only [add_zero]

theorem pairMergeCheck292 : pairMerged292 = Integer.Sparse.merge (Integer.Sparse.scale (5472684) (rows 43)) (Integer.Sparse.scale (166320) (rows 45)) := by decide +kernel

theorem pairMergedZero292 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged292 x = 0 := by
  rw [pairMergeCheck292, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck293 : pairMerged293 = Integer.Sparse.merge (Integer.Sparse.scale (277830) (rows 42)) pairMerged292 := by decide +kernel

theorem pairMergedZero293 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged293 x = 0 := by
  rw [pairMergeCheck293, Integer.Sparse.eval_merge]
  rw [pairMergedZero292 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck294 : pairMerged294 = Integer.Sparse.merge (Integer.Sparse.scale (399168) (rows 46)) (Integer.Sparse.scale (-212058) (rows 47)) := by decide +kernel

theorem pairMergedZero294 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged294 x = 0 := by
  rw [pairMergeCheck294, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck295 : pairMerged295 = Integer.Sparse.merge (Integer.Sparse.scale (-117936) (rows 48)) (Integer.Sparse.scale (184464) (rows 49)) := by decide +kernel

theorem pairMergedZero295 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged295 x = 0 := by
  rw [pairMergeCheck295, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck296 : pairMerged296 = Integer.Sparse.merge pairMerged294 pairMerged295 := by decide +kernel

theorem pairMergedZero296 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged296 x = 0 := by
  rw [pairMergeCheck296, Integer.Sparse.eval_merge]
  rw [pairMergedZero294 x h, pairMergedZero295 x h]
  simp only [add_zero]

theorem pairMergeCheck297 : pairMerged297 = Integer.Sparse.merge pairMerged293 pairMerged296 := by decide +kernel

theorem pairMergedZero297 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged297 x = 0 := by
  rw [pairMergeCheck297, Integer.Sparse.eval_merge]
  rw [pairMergedZero293 x h, pairMergedZero296 x h]
  simp only [add_zero]

theorem pairMergeCheck298 : pairMerged298 = Integer.Sparse.merge (Integer.Sparse.scale (-567000) (rows 51)) (Integer.Sparse.scale (-15876) (rows 52)) := by decide +kernel

theorem pairMergedZero298 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged298 x = 0 := by
  rw [pairMergeCheck298, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck299 : pairMerged299 = Integer.Sparse.merge (Integer.Sparse.scale (155358) (rows 50)) pairMerged298 := by decide +kernel

theorem pairMergedZero299 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged299 x = 0 := by
  rw [pairMergeCheck299, Integer.Sparse.eval_merge]
  rw [pairMergedZero298 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck300 : pairMerged300 = Integer.Sparse.merge (Integer.Sparse.scale (-8134560) (rows 53)) (Integer.Sparse.scale (-579474) (rows 54)) := by decide +kernel

theorem pairMergedZero300 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged300 x = 0 := by
  rw [pairMergeCheck300, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck301 : pairMerged301 = Integer.Sparse.merge (Integer.Sparse.scale (-1623888) (rows 55)) (Integer.Sparse.scale (408240) (rows 57)) := by decide +kernel

theorem pairMergedZero301 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged301 x = 0 := by
  rw [pairMergeCheck301, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck302 : pairMerged302 = Integer.Sparse.merge pairMerged300 pairMerged301 := by decide +kernel

theorem pairMergedZero302 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged302 x = 0 := by
  rw [pairMergeCheck302, Integer.Sparse.eval_merge]
  rw [pairMergedZero300 x h, pairMergedZero301 x h]
  simp only [add_zero]

theorem pairMergeCheck303 : pairMerged303 = Integer.Sparse.merge pairMerged299 pairMerged302 := by decide +kernel

theorem pairMergedZero303 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged303 x = 0 := by
  rw [pairMergeCheck303, Integer.Sparse.eval_merge]
  rw [pairMergedZero299 x h, pairMergedZero302 x h]
  simp only [add_zero]

theorem pairMergeCheck304 : pairMerged304 = Integer.Sparse.merge pairMerged297 pairMerged303 := by decide +kernel

theorem pairMergedZero304 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged304 x = 0 := by
  rw [pairMergeCheck304, Integer.Sparse.eval_merge]
  rw [pairMergedZero297 x h, pairMergedZero303 x h]
  simp only [add_zero]

theorem pairMergeCheck305 : pairMerged305 = Integer.Sparse.merge pairMerged291 pairMerged304 := by decide +kernel

theorem pairMergedZero305 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged305 x = 0 := by
  rw [pairMergeCheck305, Integer.Sparse.eval_merge]
  rw [pairMergedZero291 x h, pairMergedZero304 x h]
  simp only [add_zero]

theorem pairMergeCheck306 : pairMerged306 = Integer.Sparse.merge pairMerged279 pairMerged305 := by decide +kernel

theorem pairMergedZero306 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged306 x = 0 := by
  rw [pairMergeCheck306, Integer.Sparse.eval_merge]
  rw [pairMergedZero279 x h, pairMergedZero305 x h]
  simp only [add_zero]

theorem pairMergeCheck307 : pairMerged307 = Integer.Sparse.merge (Integer.Sparse.scale (10670940) (rows 59)) (Integer.Sparse.scale (1762992) (rows 60)) := by decide +kernel

theorem pairMergedZero307 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged307 x = 0 := by
  rw [pairMergeCheck307, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck308 : pairMerged308 = Integer.Sparse.merge (Integer.Sparse.scale (513702) (rows 58)) pairMerged307 := by decide +kernel

theorem pairMergedZero308 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged308 x = 0 := by
  rw [pairMergeCheck308, Integer.Sparse.eval_merge]
  rw [pairMergedZero307 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck309 : pairMerged309 = Integer.Sparse.merge (Integer.Sparse.scale (5288976) (rows 62)) (Integer.Sparse.scale (4604040) (rows 63)) := by decide +kernel

theorem pairMergedZero309 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged309 x = 0 := by
  rw [pairMergeCheck309, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck310 : pairMerged310 = Integer.Sparse.merge (Integer.Sparse.scale (3900960) (rows 61)) pairMerged309 := by decide +kernel

theorem pairMergedZero310 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged310 x = 0 := by
  rw [pairMergeCheck310, Integer.Sparse.eval_merge]
  rw [pairMergedZero309 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck311 : pairMerged311 = Integer.Sparse.merge pairMerged308 pairMerged310 := by decide +kernel

theorem pairMergedZero311 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged311 x = 0 := by
  rw [pairMergeCheck311, Integer.Sparse.eval_merge]
  rw [pairMergedZero308 x h, pairMergedZero310 x h]
  simp only [add_zero]

theorem pairMergeCheck312 : pairMerged312 = Integer.Sparse.merge (Integer.Sparse.scale (585144) (rows 67)) (Integer.Sparse.scale (-12678120) (rows 68)) := by decide +kernel

theorem pairMergedZero312 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged312 x = 0 := by
  rw [pairMergeCheck312, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck313 : pairMerged313 = Integer.Sparse.merge (Integer.Sparse.scale (-3525984) (rows 65)) pairMerged312 := by decide +kernel

theorem pairMergedZero313 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged313 x = 0 := by
  rw [pairMergeCheck313, Integer.Sparse.eval_merge]
  rw [pairMergedZero312 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck314 : pairMerged314 = Integer.Sparse.merge (Integer.Sparse.scale (31026240) (rows 69)) (Integer.Sparse.scale (1623888) (rows 71)) := by decide +kernel

theorem pairMergedZero314 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged314 x = 0 := by
  rw [pairMergeCheck314, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck315 : pairMerged315 = Integer.Sparse.merge (Integer.Sparse.scale (-458136) (rows 72)) (Integer.Sparse.scale (229068) (rows 74)) := by decide +kernel

theorem pairMergedZero315 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged315 x = 0 := by
  rw [pairMergeCheck315, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck316 : pairMerged316 = Integer.Sparse.merge pairMerged314 pairMerged315 := by decide +kernel

theorem pairMergedZero316 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged316 x = 0 := by
  rw [pairMergeCheck316, Integer.Sparse.eval_merge]
  rw [pairMergedZero314 x h, pairMergedZero315 x h]
  simp only [add_zero]

theorem pairMergeCheck317 : pairMerged317 = Integer.Sparse.merge pairMerged313 pairMerged316 := by decide +kernel

theorem pairMergedZero317 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged317 x = 0 := by
  rw [pairMergeCheck317, Integer.Sparse.eval_merge]
  rw [pairMergedZero313 x h, pairMergedZero316 x h]
  simp only [add_zero]

theorem pairMergeCheck318 : pairMerged318 = Integer.Sparse.merge pairMerged311 pairMerged317 := by decide +kernel

theorem pairMergedZero318 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged318 x = 0 := by
  rw [pairMergeCheck318, Integer.Sparse.eval_merge]
  rw [pairMergedZero311 x h, pairMergedZero317 x h]
  simp only [add_zero]

theorem pairMergeCheck319 : pairMerged319 = Integer.Sparse.merge (Integer.Sparse.scale (-838026) (rows 76)) (Integer.Sparse.scale (-3433185) (rows 77)) := by decide +kernel

theorem pairMergedZero319 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged319 x = 0 := by
  rw [pairMergeCheck319, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck320 : pairMerged320 = Integer.Sparse.merge (Integer.Sparse.scale (768852) (rows 75)) pairMerged319 := by decide +kernel

theorem pairMergedZero320 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged320 x = 0 := by
  rw [pairMergeCheck320, Integer.Sparse.eval_merge]
  rw [pairMergedZero319 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck321 : pairMerged321 = Integer.Sparse.merge (Integer.Sparse.scale (-561330) (rows 78)) (Integer.Sparse.scale (2806650) (rows 79)) := by decide +kernel

theorem pairMergedZero321 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged321 x = 0 := by
  rw [pairMergeCheck321, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck322 : pairMerged322 = Integer.Sparse.merge (Integer.Sparse.scale (4320540) (rows 80)) (Integer.Sparse.scale (-10560375) (rows 81)) := by decide +kernel

theorem pairMergedZero322 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged322 x = 0 := by
  rw [pairMergeCheck322, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck323 : pairMerged323 = Integer.Sparse.merge pairMerged321 pairMerged322 := by decide +kernel

theorem pairMergedZero323 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged323 x = 0 := by
  rw [pairMergeCheck323, Integer.Sparse.eval_merge]
  rw [pairMergedZero321 x h, pairMergedZero322 x h]
  simp only [add_zero]

theorem pairMergeCheck324 : pairMerged324 = Integer.Sparse.merge pairMerged320 pairMerged323 := by decide +kernel

theorem pairMergedZero324 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged324 x = 0 := by
  rw [pairMergeCheck324, Integer.Sparse.eval_merge]
  rw [pairMergedZero320 x h, pairMergedZero323 x h]
  simp only [add_zero]

theorem pairMergeCheck325 : pairMerged325 = Integer.Sparse.merge (Integer.Sparse.scale (1122660) (rows 83)) (Integer.Sparse.scale (-1296162) (rows 84)) := by decide +kernel

theorem pairMergedZero325 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged325 x = 0 := by
  rw [pairMergeCheck325, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck326 : pairMerged326 = Integer.Sparse.merge (Integer.Sparse.scale (838026) (rows 82)) pairMerged325 := by decide +kernel

theorem pairMergedZero326 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged326 x = 0 := by
  rw [pairMergeCheck326, Integer.Sparse.eval_merge]
  rw [pairMergedZero325 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck327 : pairMerged327 = Integer.Sparse.merge (Integer.Sparse.scale (-1551312) (rows 85)) (Integer.Sparse.scale (1093176) (rows 86)) := by decide +kernel

theorem pairMergedZero327 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged327 x = 0 := by
  rw [pairMergeCheck327, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck328 : pairMerged328 = Integer.Sparse.merge (Integer.Sparse.scale (458136) (rows 87)) (Integer.Sparse.scale (2129652) (rows 89)) := by decide +kernel

theorem pairMergedZero328 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged328 x = 0 := by
  rw [pairMergeCheck328, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck329 : pairMerged329 = Integer.Sparse.merge pairMerged327 pairMerged328 := by decide +kernel

theorem pairMergedZero329 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged329 x = 0 := by
  rw [pairMergeCheck329, Integer.Sparse.eval_merge]
  rw [pairMergedZero327 x h, pairMergedZero328 x h]
  simp only [add_zero]

theorem pairMergeCheck330 : pairMerged330 = Integer.Sparse.merge pairMerged326 pairMerged329 := by decide +kernel

theorem pairMergedZero330 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged330 x = 0 := by
  rw [pairMergeCheck330, Integer.Sparse.eval_merge]
  rw [pairMergedZero326 x h, pairMergedZero329 x h]
  simp only [add_zero]

theorem pairMergeCheck331 : pairMerged331 = Integer.Sparse.merge pairMerged324 pairMerged330 := by decide +kernel

theorem pairMergedZero331 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged331 x = 0 := by
  rw [pairMergeCheck331, Integer.Sparse.eval_merge]
  rw [pairMergedZero324 x h, pairMergedZero330 x h]
  simp only [add_zero]

theorem pairMergeCheck332 : pairMerged332 = Integer.Sparse.merge pairMerged318 pairMerged331 := by decide +kernel

theorem pairMergedZero332 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged332 x = 0 := by
  rw [pairMergeCheck332, Integer.Sparse.eval_merge]
  rw [pairMergedZero318 x h, pairMergedZero331 x h]
  simp only [add_zero]

theorem pairMergeCheck333 : pairMerged333 = Integer.Sparse.merge (Integer.Sparse.scale (-360612) (rows 91)) (Integer.Sparse.scale (405972) (rows 92)) := by decide +kernel

theorem pairMergedZero333 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged333 x = 0 := by
  rw [pairMergeCheck333, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck334 : pairMerged334 = Integer.Sparse.merge (Integer.Sparse.scale (458136) (rows 90)) pairMerged333 := by decide +kernel

theorem pairMergedZero334 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged334 x = 0 := by
  rw [pairMergeCheck334, Integer.Sparse.eval_merge]
  rw [pairMergedZero333 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck335 : pairMerged335 = Integer.Sparse.merge (Integer.Sparse.scale (-2041200) (rows 96)) (Integer.Sparse.scale (-1796256) (rows 97)) := by decide +kernel

theorem pairMergedZero335 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged335 x = 0 := by
  rw [pairMergeCheck335, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck336 : pairMerged336 = Integer.Sparse.merge (Integer.Sparse.scale (-3075408) (rows 93)) pairMerged335 := by decide +kernel

theorem pairMergedZero336 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged336 x = 0 := by
  rw [pairMergeCheck336, Integer.Sparse.eval_merge]
  rw [pairMergedZero335 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck337 : pairMerged337 = Integer.Sparse.merge pairMerged334 pairMerged336 := by decide +kernel

theorem pairMergedZero337 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged337 x = 0 := by
  rw [pairMergeCheck337, Integer.Sparse.eval_merge]
  rw [pairMergedZero334 x h, pairMergedZero336 x h]
  simp only [add_zero]

theorem pairMergeCheck338 : pairMerged338 = Integer.Sparse.merge (Integer.Sparse.scale (-1728216) (rows 99)) (Integer.Sparse.scale (1122660) (rows 100)) := by decide +kernel

theorem pairMergedZero338 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged338 x = 0 := by
  rw [pairMergeCheck338, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck339 : pairMerged339 = Integer.Sparse.merge (Integer.Sparse.scale (2806650) (rows 98)) pairMerged338 := by decide +kernel

theorem pairMergedZero339 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged339 x = 0 := by
  rw [pairMergeCheck339, Integer.Sparse.eval_merge]
  rw [pairMergedZero338 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck340 : pairMerged340 = Integer.Sparse.merge (Integer.Sparse.scale (-3375540) (rows 101)) (Integer.Sparse.scale (360612) (rows 102)) := by decide +kernel

theorem pairMergedZero340 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged340 x = 0 := by
  rw [pairMergeCheck340, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck341 : pairMerged341 = Integer.Sparse.merge (Integer.Sparse.scale (56700) (rows 103)) (Integer.Sparse.scale (27216) (rows 104)) := by decide +kernel

theorem pairMergedZero341 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged341 x = 0 := by
  rw [pairMergeCheck341, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck342 : pairMerged342 = Integer.Sparse.merge pairMerged340 pairMerged341 := by decide +kernel

theorem pairMergedZero342 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged342 x = 0 := by
  rw [pairMergeCheck342, Integer.Sparse.eval_merge]
  rw [pairMergedZero340 x h, pairMergedZero341 x h]
  simp only [add_zero]

theorem pairMergeCheck343 : pairMerged343 = Integer.Sparse.merge pairMerged339 pairMerged342 := by decide +kernel

theorem pairMergedZero343 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged343 x = 0 := by
  rw [pairMergeCheck343, Integer.Sparse.eval_merge]
  rw [pairMergedZero339 x h, pairMergedZero342 x h]
  simp only [add_zero]

theorem pairMergeCheck344 : pairMerged344 = Integer.Sparse.merge pairMerged337 pairMerged343 := by decide +kernel

theorem pairMergedZero344 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged344 x = 0 := by
  rw [pairMergeCheck344, Integer.Sparse.eval_merge]
  rw [pairMergedZero337 x h, pairMergedZero343 x h]
  simp only [add_zero]

theorem pairMergeCheck345 : pairMerged345 = Integer.Sparse.merge (Integer.Sparse.scale (-38556) (rows 107)) (Integer.Sparse.scale (-158760) (rows 109)) := by decide +kernel

theorem pairMergedZero345 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged345 x = 0 := by
  rw [pairMergeCheck345, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck346 : pairMerged346 = Integer.Sparse.merge (Integer.Sparse.scale (1360800) (rows 105)) pairMerged345 := by decide +kernel

theorem pairMergedZero346 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged346 x = 0 := by
  rw [pairMergeCheck346, Integer.Sparse.eval_merge]
  rw [pairMergedZero345 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck347 : pairMerged347 = Integer.Sparse.merge (Integer.Sparse.scale (-113400) (rows 110)) (Integer.Sparse.scale (-272160) (rows 111)) := by decide +kernel

theorem pairMergedZero347 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged347 x = 0 := by
  rw [pairMergeCheck347, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck348 : pairMerged348 = Integer.Sparse.merge (Integer.Sparse.scale (77112) (rows 112)) (Integer.Sparse.scale (-408240) (rows 113)) := by decide +kernel

theorem pairMergedZero348 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged348 x = 0 := by
  rw [pairMergeCheck348, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck349 : pairMerged349 = Integer.Sparse.merge pairMerged347 pairMerged348 := by decide +kernel

theorem pairMergedZero349 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged349 x = 0 := by
  rw [pairMergeCheck349, Integer.Sparse.eval_merge]
  rw [pairMergedZero347 x h, pairMergedZero348 x h]
  simp only [add_zero]

theorem pairMergeCheck350 : pairMerged350 = Integer.Sparse.merge pairMerged346 pairMerged349 := by decide +kernel

theorem pairMergedZero350 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged350 x = 0 := by
  rw [pairMergeCheck350, Integer.Sparse.eval_merge]
  rw [pairMergedZero346 x h, pairMergedZero349 x h]
  simp only [add_zero]

theorem pairMergeCheck351 : pairMerged351 = Integer.Sparse.merge (Integer.Sparse.scale (-47628) (rows 115)) (Integer.Sparse.scale (-108864) (rows 116)) := by decide +kernel

theorem pairMergedZero351 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged351 x = 0 := by
  rw [pairMergeCheck351, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck352 : pairMerged352 = Integer.Sparse.merge (Integer.Sparse.scale (170100) (rows 114)) pairMerged351 := by decide +kernel

theorem pairMergedZero352 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged352 x = 0 := by
  rw [pairMergeCheck352, Integer.Sparse.eval_merge]
  rw [pairMergedZero351 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck353 : pairMerged353 = Integer.Sparse.merge (Integer.Sparse.scale (27216) (rows 123)) (Integer.Sparse.scale (1156680) (rows 128)) := by decide +kernel

theorem pairMergedZero353 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged353 x = 0 := by
  rw [pairMergeCheck353, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck354 : pairMerged354 = Integer.Sparse.merge (Integer.Sparse.scale (-1156680) (rows 129)) (Integer.Sparse.scale (-54432) (rows 130)) := by decide +kernel

theorem pairMergedZero354 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged354 x = 0 := by
  rw [pairMergeCheck354, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck355 : pairMerged355 = Integer.Sparse.merge pairMerged353 pairMerged354 := by decide +kernel

theorem pairMergedZero355 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged355 x = 0 := by
  rw [pairMergeCheck355, Integer.Sparse.eval_merge]
  rw [pairMergedZero353 x h, pairMergedZero354 x h]
  simp only [add_zero]

theorem pairMergeCheck356 : pairMerged356 = Integer.Sparse.merge pairMerged352 pairMerged355 := by decide +kernel

theorem pairMergedZero356 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged356 x = 0 := by
  rw [pairMergeCheck356, Integer.Sparse.eval_merge]
  rw [pairMergedZero352 x h, pairMergedZero355 x h]
  simp only [add_zero]

theorem pairMergeCheck357 : pairMerged357 = Integer.Sparse.merge pairMerged350 pairMerged356 := by decide +kernel

theorem pairMergedZero357 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged357 x = 0 := by
  rw [pairMergeCheck357, Integer.Sparse.eval_merge]
  rw [pairMergedZero350 x h, pairMergedZero356 x h]
  simp only [add_zero]

theorem pairMergeCheck358 : pairMerged358 = Integer.Sparse.merge pairMerged344 pairMerged357 := by decide +kernel

theorem pairMergedZero358 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged358 x = 0 := by
  rw [pairMergeCheck358, Integer.Sparse.eval_merge]
  rw [pairMergedZero344 x h, pairMergedZero357 x h]
  simp only [add_zero]

theorem pairMergeCheck359 : pairMerged359 = Integer.Sparse.merge pairMerged332 pairMerged358 := by decide +kernel

theorem pairMergedZero359 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged359 x = 0 := by
  rw [pairMergeCheck359, Integer.Sparse.eval_merge]
  rw [pairMergedZero332 x h, pairMergedZero358 x h]
  simp only [add_zero]

theorem pairMergeCheck360 : pairMerged360 = Integer.Sparse.merge pairMerged306 pairMerged359 := by decide +kernel

theorem pairMergedZero360 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged360 x = 0 := by
  rw [pairMergeCheck360, Integer.Sparse.eval_merge]
  rw [pairMergedZero306 x h, pairMergedZero359 x h]
  simp only [add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairTargetPermutation1 : List.Perm target1 pairMerged360 := by decide +kernel

theorem mergeConsequence1 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval target1 x = 0 := by
  rw [Integer.Sparse.eval_perm pairTargetPermutation1]
  exact pairMergedZero360 x h

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem targetZero1 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval PairData.target1 (momentVector H) = 0 :=
  PairData.mergeConsequence1 _ (allRowsSound_e hH)

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem finalReindex1 : List.Perm
    (Integer.Sparse.reindex PairSourceBridge.coordinateMap PairData.target1) integerMerge49 := by decide +kernel

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem certificate_zero1 {H : CMatrix} (hH : IsHadamard H) : expanded1 H = 0 := by
  have hz := PairSourceBridge.targetZero1 hH
  unfold PairSourceBridge.momentVector at hz
  rw [← Integer.Sparse.eval_reindex] at hz
  rw [Integer.Sparse.eval_perm finalReindex1] at hz
  have he := expandedIdentity1_e hH
  rw [hz] at he
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_FourierTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem pair_same_certificate {H : CMatrix} (hH : IsHadamard H) :
    PairCertificateIdentity H qSame := by
  unfold PairCertificateIdentity
  rw [← Certificate.PairTargetSemantics.expanded_identity1 hH]
  exact Certificate.PairTargetSemantics.certificate_zero1 hH

/-- Endpoint 1: arbitrary complex entries, full Hadamard equivalence, and the
manuscript's normalized Fourier coefficient for every permuted alpha. -/
theorem fourier_vanishing {H : CMatrix} (hH : IsHadamard H)
    (hTao : ¬Equivalent H tao) (π : Equiv.Perm Coord) :
    g H (permuteCharge π alpha) = 0 :=
  fourier_vanishing_of_pair_certificates hH
    (pair_cross_certificate_e hH) (pair_same_certificate hH) hTao π

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6

theorem fourier_and_family_bound_oai :
    (∀ H : CMatrix, IsHadamard H → ¬Equivalent H tao →
      ∀ π : Equiv.Perm Coord, g H (permuteCharge π alpha) = 0) ∧
    (∀ n : ℕ, Attainable n → n ≤ 5) := by
  constructor
  · intro H hH hTao π
    exact fourier_vanishing hH hTao π
  · exact family_size_le_five_e

end MUB6

end OAI
end

theorem solution : type_of% @OAI.MUB6.fourier_and_family_bound_oai := @OAI.MUB6.fourier_and_family_bound_oai
