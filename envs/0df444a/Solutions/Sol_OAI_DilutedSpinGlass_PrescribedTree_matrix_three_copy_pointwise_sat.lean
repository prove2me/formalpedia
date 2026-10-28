-- Prove2me | solution 1 for OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:36:02.498981+00:00
-- url     : https://prove2.me/submissions/d56c2f6e-2830-4a81-a8b4-0494c94f52b9

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Theorems.Thm_OAI_DilutedSpinGlass_PrescribedTree_matrixHistory_first_pair_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

variable {n : ℕ}

/-- Finite-law Cauchy-Schwarz. -/
theorem expect_mul_sq_le (f g : Ω → ℝ) :
    P.expect (fun x => f x * g x)^2 ≤
      P.expect (fun x => f x^2) * P.expect (fun x => g x^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (P.weight x) * f x)
    (fun x => Real.sqrt (P.weight x) * g x)
  have hm (x : Ω) : Real.sqrt (P.weight x) * f x *
      (Real.sqrt (P.weight x) * g x) = P.weight x * (f x * g x) := by
    calc
      _ = Real.sqrt (P.weight x)^2 * (f x * g x) := by ring
      _ = _ := by rw [Real.sq_sqrt (P.nonneg x)]
  simpa only [hm, mul_pow, Real.sq_sqrt (P.nonneg _), expect] using h

theorem l2_nonneg (f : Ω → ℝ) : 0 ≤ P.l2 f := Real.sqrt_nonneg _

/-- Finite independence identity, valid for arbitrary and distinct kernels. -/
theorem expect_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → ℝ) :
    (pi Q).expect (fun x => ∏ i, f i (x i)) = ∏ i, (Q i).expect (f i) := by
  simp only [expect, pi, ← Finset.prod_mul_distrib, Fintype.prod_sum]

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProducts
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

/-- Fubini at an arbitrary coordinate, retaining dependent finite sample types. -/
theorem expect_pi_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (Q : (i : ι) → FiniteLaw (α i))
    (i : ι) (H : ((i : ι) → α i) → ℝ) :
    (pi Q).expect H = (Q i).expect (fun a =>
      (pi (fun j : {j // j ≠ i} => Q j)).expect
        (fun rest => H ((Equiv.piSplitAt i α).symm (a,rest)))) := by
  classical
  have hprod (x : (i : ι) → α i) :
      (∏ j, (Q j).weight (x j)) =
        (Q i).weight (x i) * ∏ j : {j // j ≠ i}, (Q j).weight (x j) := by
    let : Fintype {j : ι // j = i} := Subtype.fintype (fun j => j = i)
    have hh := Fintype.prod_subtype_mul_prod_subtype (fun j => j = i)
      (fun j => (Q j).weight (x j))
    rw [Fintype.prod_subsingleton _ ⟨i,rfl⟩] at hh
    exact hh.symm
  simp only [expect, pi]
  rw [← (Equiv.piSplitAt i α).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [hprod]
  have hh : (∏ j : {j // j ≠ i}, (Q j).weight
      ((Equiv.piSplitAt i α).symm (a,rest) j)) =
      ∏ j : {j // j ≠ i}, (Q j).weight (rest j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [Equiv.piSplitAt_symm_apply, dite_eq_right j.property]
  rw [hh]
  simp only [Equiv.piSplitAt_symm_apply, dite_true]
  ring

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

private theorem delta_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    (x y : (i : ι) → α i) :
    (∏ i, delta (x i) (y i)) = delta x y := by
  classical
  by_cases h : x = y
  · subst y
    simp [delta]
  · have hn : ∃ i, x i ≠ y i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i,hi⟩ := hn
    rw [delta, ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [delta,hi])

private theorem expand_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (H : ((i : ι) → α i) → ℝ)
    (x : (i : ι) → α i) : H x = ∑ y, H y * ∏ i, delta (x i) (y i) := by
  classical
  simp_rw [delta_pi]
  simp [delta]

private theorem expect_pi_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (P : (i : ι) → FiniteLaw (α i)) (φ : (i : ι) → α i → β i)
    (w : (i : ι) → α i → ℝ) (H : ((i : ι) → β i) → ℝ) :
    (pi P).expect (fun x => H (fun i => φ i (x i)) * ∏ i, w i (x i)) =
      ∑ y, H y * ∏ i, (P i).expect (fun x => w i x * delta (φ i x) (y i)) := by
  classical
  have heq (x : (i : ι) → α i) :
      H (fun i => φ i (x i)) * (∏ i, w i (x i)) =
        ∑ y, H y * ∏ i, (w i (x i) * delta (φ i (x i)) (y i)) := by
    rw [expand_pi H (fun i => φ i (x i)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.prod_mul_distrib]
    ring
  rw [(pi P).expect_congr heq]
  simp only [expect_fintype_sum, expect_mul_left]
  apply Finset.sum_congr rfl
  intro y _
  rw [expect_pi_product P (fun i x => w i x * delta (φ i x) (y i))]

/-- Tensorization of arbitrary signed one-coordinate changes. This permits
inserting a marked new branch at a single child without assuming the test
factors across the old children. -/
theorem expect_pi_weighted_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (P : (i : ι) → FiniteLaw (α i)) (Q : (i : ι) → FiniteLaw (β i))
    (φ : (i : ι) → α i → β i) (w : (i : ι) → α i → ℝ) (v : (i : ι) → β i → ℝ)
    (h : ∀ i (g : β i → ℝ), (P i).expect (fun x => w i x * g (φ i x)) =
      (Q i).expect (fun y => v i y * g y)) (H : ((i : ι) → β i) → ℝ) :
    (pi P).expect (fun x => H (fun i => φ i (x i)) * ∏ i, w i (x i)) =
      (pi Q).expect (fun y => H y * ∏ i, v i (y i)) := by
  rw [expect_pi_expand P φ w H, expect_pi_expand Q (fun _ y => y) v H]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact h i (fun x => delta x (y i))

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw

theorem expect_pi_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (P : (i : ι) → FiniteLaw (α i))
    (i : ι) (f : α i → ℝ) : (pi P).expect (fun x => f (x i)) = (P i).expect f := by
  erw [expect_pi_split P i]
  simp! only [Equiv.piSplitAt_symm_apply, dite_true, expect_const]

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeDerivatives
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- A single uncontracted tree samples exactly a whole conditional path. -/
theorem single_expect (n : ℕ) (T : KernelTower Ω n) (D : FinitePath Ω n → ℝ) :
    (sampleLaw (single n) T).expect (fun x => D (singlePath n x)) =
      (KernelTower.law n T).expect D := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases T with ⟨μ,K⟩
    change (FiniteLaw.pi (fun _ : Fin 1 => μ.bind
      (fun z => sampleLaw (single n) (K z)))).expect
        (fun x => D ((x 0).1,singlePath n (x 0).2)) = _
    have e := FiniteLaw.expect_pi_marginal
      (fun _ : Fin 1 => μ.bind (fun z => sampleLaw (single n) (K z))) (0 : Fin 1)
      (fun y => D (y.1,singlePath n y.2))
    refine e.trans ?_
    erw [FiniteLaw.expect_bind]
    erw [KernelTower.law_succ_expect]
    change μ.expect (fun z => _) = μ.expect (fun z => _)
    apply FiniteLaw.expect_congr
    intro z
    exact ih (K z) (fun y => D (z,y))

private theorem bind_expect_cast {n : ℕ} (S S' : PrescribedTree n) (h : S' = S)
    (μ : FiniteLaw Ω) (K : Ω → KernelTower Ω n) (f : Ω × Sample Ω S → ℝ) :
    (μ.bind (fun z => sampleLaw S' (K z))).expect
      (fun x => f (cast (congrArg (fun R => Ω × Sample Ω R) h) x)) =
    (μ.bind (fun z => sampleLaw S (K z))).expect f := by
  subst S'
  rfl

/-- The operational extension identity. New descendants are sampled afresh
conditional on their shared prefix; no assumption is made about the old test. -/
theorem extension_sampling {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (v : Internal S) (H : Sample Ω S → ℝ) (D : FinitePath Ω n → ℝ) :
    (sampleLaw (grow S v) T).expect (fun x => H (oldSample S v x) * D (newPath S v x)) =
      (sampleLaw S T).expect (fun x => H x * freshEval S T v D x) := by
  classical
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      let α : Fin (k+1) → Type := fun j => Ω × Sample Ω (Fin.cases (single n) C j)
      let Q : (j : Fin (k+1)) → FiniteLaw (α j) := fun j => μ.bind
        (fun z => sampleLaw (Fin.cases (single n) C j) (K z))
      change (FiniteLaw.pi Q).expect _ = _
      erw [FiniteLaw.expect_pi_cons]
      have he : (μ.bind (fun z => sampleLaw (single n) (K z))).expect
          (fun y => D (y.1,singlePath n y.2)) = (KernelTower.law (n+1) (μ,K)).expect D := by
        erw [FiniteLaw.expect_bind]
        erw [KernelTower.law_succ_expect]
        apply FiniteLaw.expect_congr
        intro z
        exact single_expect n (K z) (fun y => D (z,y))
      change (μ.bind (fun z => sampleLaw (single n) (K z))).expect
          (fun a => (sampleLaw (.node k C) (μ,K)).expect
            (fun rest => H rest * D (a.1,singlePath n a.2))) =
          (sampleLaw (.node k C) (μ,K)).expect (fun x => H x * (KernelTower.law (n+1) (μ,K)).expect D)
      simp! only [FiniteLaw.expect_mul_right, FiniteLaw.expect_mul_left, he]
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      let P (j : Fin k) := μ.bind (fun z => sampleLaw (C' j) (K z))
      let Q (j : Fin k) := μ.bind (fun z => sampleLaw (C j) (K z))
      let φ (j : Fin k) : Ω × Sample Ω (C' j) → Ω × Sample Ω (C j) := by
        intro y
        by_cases hj : j = i
        · subst j
          have yy : Ω × Sample Ω (grow (C i) v) := by simpa! only [C', Function.update_self] using y
          exact (yy.1, oldSample (C i) v yy.2)
        · exact cast (by simp! only [C', Function.update_of_ne hj]) y
      let W (j : Fin k) : Ω × Sample Ω (C' j) → ℝ := by
        intro y
        by_cases hj : j = i
        · subst j
          have yy : Ω × Sample Ω (grow (C i) v) := by simpa! only [C', Function.update_self] using y
          exact D (yy.1, newPath (C i) v yy.2)
        · exact 1
      let V (j : Fin k) : Ω × Sample Ω (C j) → ℝ := by
        intro y
        by_cases hj : j = i
        · subst j
          exact freshEval (C i) (K y.1) v (fun z => D (y.1,z)) y.2
        · exact 1
      have hchanged : ∀ j (g : Ω × Sample Ω (C j) → ℝ),
          (P j).expect (fun x => W j x * g (φ j x)) =
            (Q j).expect (fun y => V j y * g y) := by
        intro j g
        by_cases hj : j = i
        · subst j
          have e : (μ.bind (fun z => sampleLaw (grow (C i) v) (K z))).expect
              (fun x => D (x.1,newPath (C i) v x.2) * g (x.1,oldSample (C i) v x.2)) =
              (Q i).expect (fun y => freshEval (C i) (K y.1) v (fun z => D (y.1,z)) y.2 * g y) := by
            simp! only [Q, FiniteLaw.expect_bind]
            apply FiniteLaw.expect_congr
            intro z
            calc
              _ = (sampleLaw (grow (C i) v) (K z)).expect
                  (fun y => g (z,oldSample (C i) v y) * D (z,newPath (C i) v y)) :=
                FiniteLaw.expect_congr _ (fun _ => mul_comm _ _)
              _ = _ := (ih i (K z) v (fun y => g (z,y)) (fun y => D (z,y))).trans
                (FiniteLaw.expect_congr _ (fun _ => mul_comm _ _))
          have hc := bind_expect_cast (grow (C i) v) (C' i)
            (Function.update_self ..) μ K
            (fun x => D (x.1,newPath (C i) v x.2) * g (x.1,oldSample (C i) v x.2))
          exact (show (P i).expect (fun x => W i x * g (φ i x)) = _ from by
            simp only [W, φ, dite_eq_left rfl]
            exact hc).trans (by
              simpa only [V, dite_eq_left rfl] using e)
        · have hc := bind_expect_cast (C j) (C' j)
            (Function.update_of_ne hj ..) μ K g
          simpa only [W, V, φ, dite_eq_right hj, one_mul] using hc
      have ht := FiniteLaw.expect_pi_weighted_map P Q φ W V hchanged H
      have hp (x : Sample Ω (grow (.node k C) (some ⟨i,v⟩))) :
          oldSample (.node k C) (some ⟨i,v⟩) x = fun j => φ j (x j) := by
        funext j
        by_cases hj : j = i
        · subst j
          erw [oldSample.eq_1]
          dsimp only [id]
          simp only [φ, dite_eq_left rfl, dite_true]
        · erw [oldSample.eq_1]
          dsimp only [id]
          simp only [φ, dite_eq_right hj]
          rfl
      have hw (x : Sample Ω (grow (.node k C) (some ⟨i,v⟩))) :
          (∏ j, W j (x j)) = D (newPath (.node k C) (some ⟨i,v⟩) x) := by
        erw [Finset.prod_eq_single i]
        · erw [newPath.eq_1]
          dsimp! only
          simp! only [W, dite_eq_left rfl]
          rfl
        · intro j _ hj
          simp! only [W, dite_eq_right hj]
        · simp
      have hv (x : Sample Ω (.node k C)) :
          (∏ j, V j (x j)) = freshEval (.node k C) (μ,K) (some ⟨i,v⟩) D x := by
        erw [Finset.prod_eq_single i]
        · simp only [V, dite_eq_left rfl]
          rfl
        · intro j _ hj
          simp! only [V, dite_eq_right hj]
        · simp
      change (FiniteLaw.pi P).expect _ = (FiniteLaw.pi Q).expect _
      calc
        _ = (FiniteLaw.pi P).expect (fun x => H (fun j => φ j (x j)) * ∏ j, W j (x j)) := by
          apply FiniteLaw.expect_congr
          intro x
          exact congrArg₂ (· * ·) (congrArg H (hp x)) (hw x).symm
        _ = _ := ht
        _ = _ := FiniteLaw.expect_congr _ (fun x => congrArg (H x * ·) (hv x))

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type}

theorem leafSum_single (n : ℕ) (f : FinitePath Ω n → ℝ) (x : Sample Ω (single n)) :
    leafSum (single n) f x = f (singlePath n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∑ i : Fin 1, leafSum (single n) (fun y => f ((x i).1,y)) (x i).2) = _
    rw [Fintype.sum_subsingleton]
    exact ih _ _

private theorem leafSum_cast {n : ℕ} (S S' : PrescribedTree n) (h : S' = S)
    (f : FinitePath Ω (n+1) → ℝ) (x : Ω × Sample Ω S') :
    leafSum S' (fun y => f (x.1,y)) x.2 =
    leafSum S (fun y => f ((cast (congrArg (fun R => Ω × Sample Ω R) h) x).1,y))
      (cast (congrArg (fun R => Ω × Sample Ω R) h) x).2 := by
  subst S'
  rfl

/-- Exactly one terminal mark is added by growth, and its ancestry is the
new path, not a path chosen by equality of sample values. -/
theorem leafSum_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω (grow S v)) :
    leafSum (grow S v) f x = leafSum S f (oldSample S v x) + f (newPath S v x) := by
  classical
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (∑ j : Fin (k+1), leafSum (Fin.cases (single n) C j)
        (fun y => f ((x j).1,y)) (x j).2) = _
      erw [Fin.sum_univ_succ]
      have hh := leafSum_single n (fun y => f ((x 0).1,y)) (x 0).2
      calc
        _ = f ((x 0).1,singlePath n (x 0).2) +
            ∑ i : Fin k, leafSum (C i) (fun y => f ((x i.succ).1,y)) (x i.succ).2 :=
          congrArg₂ (· + ·) hh rfl
        _ = _ := add_comm _ _
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      have hp (j : Fin k) :
          leafSum (C' j) (fun y => f ((x j).1,y)) (x j).2 =
          leafSum (C j) (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 +
              if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 0 := by
        by_cases hj : j = i
        · subst j
          have hcast := leafSum_cast (grow (C i) v) (C' i)
            (Function.update_self ..) f (x i)
          let y : Ω × Sample Ω (grow (C i) v) :=
            cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
          have hh := ih i v (fun z => f (y.1,z)) y.2
          have he : leafSum (C' i) (fun z => f ((x i).1,z)) (x i).2 =
              leafSum (C i) (fun z => f (y.1,z)) (oldSample (C i) v y.2) +
                f (y.1,newPath (C i) v y.2) := hcast.trans hh
          erw [oldSample.eq_1, newPath.eq_1]
          dsimp only [id]
          simp only [dite_true, ite_true]
          exact he
        · have hc := leafSum_cast (C j) (C' j) (Function.update_of_ne hj ..) f (x j)
          erw [oldSample.eq_1]
          dsimp only [id]
          simp only [dite_eq_right hj, ite_eq_right hj, add_zero]
          exact hc
      change (∑ j, leafSum (C' j) (fun y => f ((x j).1,y)) (x j).2) = _
      calc
        _ = ∑ j, (leafSum (C j)
            (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 +
            if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 0) :=
          Finset.sum_congr rfl (fun j _ => hp j)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)]; rfl

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

/-- The exact signed budget for internal extensions with finite exponent indices. -/
theorem sum_gamma {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ) :
    (∑ v : Internal S, gamma S m v) = m 0 - (leaves S : ℝ) * m (Fin.last n) := by
  induction S with
  | leaf =>
    change (∑ v : Empty, gamma .leaf m v) = _
    have hs : (∑ v : Empty, gamma .leaf m v) = 0 :=
      Finset.sum_eq_zero (fun v _ => nomatch v)
    rw [hs]
    simp [leaves, Fin.last_zero]
  | @node n k C ih =>
    change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    erw [Fintype.sum_option, Fintype.sum_sigma]
    change m 0 - (k : ℝ) * m 1 +
      (∑ i, ∑ v : Internal (C i), gamma (C i) (fun j => m j.succ) v) = _
    simp_rw [ih]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin, leaves, Nat.cast_sum, Fin.succ_last, Fin.succ_zero_eq_one]
    rw [← Finset.sum_mul]
    ring

theorem gamma_nonpos {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (v : Internal S) : gamma S m v ≤ 0 := by
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change m 0 - (k : ℝ) * m 1 ≤ 0
      have hh : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.property
      have h01 := hm (show (0 : Fin (n+2)) ≤ 1 by exact Fin.zero_le _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hh) (hpos 1)]
    | some v =>
      obtain ⟨i,v⟩ := v
      exact ih i (fun j => m j.succ) (fun a b h => hm (Fin.succ_le_succ_iff.mpr h))
        (fun j => hpos j.succ) v

/-- Absolute coefficients sum to the number of old leaves. -/
theorem sum_abs_gamma {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) :
    (∑ v : Internal S, |gamma S m v|) = (leaves S : ℝ) := by
  simp_rw [abs_of_nonpos (gamma_nonpos S m hm hpos _)]
  rw [Finset.sum_neg_distrib, sum_gamma, hroot, hend]
  ring

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem leafSum_const {Ω : Type} {n : ℕ} (S : PrescribedTree n)
    (c : ℝ) (x : Sample Ω S) : leafSum S (fun _ => c) x = (leaves S : ℝ) * c := by
  induction S with
  | leaf => simp [leafSum, leaves]
  | @node n k C ih =>
    change (∑ i, leafSum (C i) (fun _ => c) (x i).2) = _
    simp_rw [ih]
    simp only [leaves, Nat.cast_sum, Finset.sum_mul]

theorem leaves_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S) :
    leaves (grow S v) = leaves S + 1 := by
  have hh := @leafSum_grow Unit n S v (fun _ => 1) (trivialSample (grow S v))
  simp only [leafSum_const, mul_one] at hh
  exact_mod_cast hh

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HistoryGeometry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace DilutedSpinGlass.PrescribedTree

variable {Ω : Type}

theorem pathAt_singleLeaf (n : ℕ) (x : Sample Ω (single n)) :
    pathAt (single n) (singleLeaf n) x = singlePath n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((x 0).1, pathAt (single n) (singleLeaf n) (x 0).2) =
      ((x 0).1, singlePath n (x 0).2)
    rw [ih]

theorem pathAt_cast {n : ℕ} (A B : PrescribedTree n) (h : B = A)
    (a : Leaf A) (x : Ω × Sample Ω B) :
    (x.1, pathAt B (cast (congrArg Leaf h.symm) a) x.2) =
      ((cast (congrArg (fun R => Ω × Sample Ω R) h) x).1,
        pathAt A a (cast (congrArg (fun R => Ω × Sample Ω R) h) x).2) := by
  subst B
  rfl

theorem pathAt_oldLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (a : Leaf S) (x : Sample Ω (grow S v)) :
    pathAt (grow S v) (oldLeaf S v a) x = pathAt S a (oldSample S v x) := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => rfl
    | some z =>
      obtain ⟨i,v⟩ := z
      obtain ⟨j,a⟩ := a
      change _ = ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,
        pathAt (C j) a (oldSample (.node k C) (some ⟨i,v⟩) x j).2)
      let C' := Function.update C i (grow (C i) v)
      by_cases h : j = i
      · subst j
        let y : Ω × Sample Ω (grow (C i) v) :=
          cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
        have hc := pathAt_cast (grow (C i) v) (C' i)
          (Function.update_self ..) (oldLeaf (C i) v a) (x i)
        have hh := congrArg (fun z => (y.1,z)) (ih i v a y.2)
        erw [oldLeaf.eq_1, oldSample.eq_1]
        dsimp only [id]
        simp only
        exact hc.trans hh
      · have hc := pathAt_cast (C j) (C' j) (Function.update_of_ne h ..) a (x j)
        erw [oldLeaf.eq_1, oldSample.eq_1]
        dsimp only [id]
        simp only [dite_eq_right h]
        exact hc

theorem pathAt_newLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (x : Sample Ω (grow S v)) :
    pathAt (grow S v) (newLeaf S v) x = newPath S v x := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact congrArg (fun y => ((x 0).1,y)) (pathAt_singleLeaf n (x 0).2)
    | some z =>
      obtain ⟨i,v⟩ := z
      let C' := Function.update C i (grow (C i) v)
      let y : Ω × Sample Ω (grow (C i) v) :=
        cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
      have hc := pathAt_cast (grow (C i) v) (C' i)
        (Function.update_self ..) (newLeaf (C i) v) (x i)
      have hh := congrArg (fun z => (y.1,z)) (ih i v y.2)
      erw [newLeaf.eq_1, newPath.eq_1]
      dsimp only [id]
      exact hc.trans hh

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable
/-- Full cancellation inside a reference-free subtree, indexed by actual
leaf positions and actual internal vertices. -/
theorem all_choices_total {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) :
    (∑ _a : Leaf S, (1 : ℝ)) + (∑ v : Internal S, gamma S m v) = m 0 := by
  have hcard : Fintype.card (Leaf S) = leaves S := by
    clear hend m
    induction S with
    | leaf => exact Fintype.card_unit
    | @node height arity children inductionHypotheses =>
      change Fintype.card ((index : Fin arity) × Leaf (children index)) = _
      simp [Fintype.card_sigma, leaves, inductionHypotheses]
  rw [sum_gamma]
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one, hend]
  ring

/-- The signed normalizing sum of ALL eligible old-or-fresh choices with a
specified deepest reference prefix is independent of all unused old branches.
Unlike reference_total, this is stated on the actual global choice indices. -/
theorem divergence_choice_total {n : ℕ} {S : PrescribedTree n}
    (D : Divergence S) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ a : Leaf S, if D.oldAllowed a then (1 : ℝ) else 0) +
      (∑ v : Internal S, if D.freshAllowed v then gamma S m v else 0) = D.coefficient m := by
  induction D with
  | @here n k C J =>
    change (∑ a : (i : Fin k) × Leaf (C i), _) +
      (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    rw [Fintype.sum_sigma, Fintype.sum_option, Fintype.sum_sigma]
    have ho_def (i : Fin k) (a : Leaf (C i)) :
        (Divergence.here J : Divergence (.node k C)).oldAllowed (⟨i,a⟩ : Leaf (.node k C)) ↔ i ∉ J := by
      erw [Divergence.oldAllowed.eq_1]
    simp_rw [ho_def]
    simp! only [Divergence.freshAllowed, Divergence.coefficient, gamma, ite_true]
    change (∑ i, ∑ _a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
      (m 0 - (k:ℝ)*m 1 + ∑ i, ∑ v : Internal (C i),
        if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0) =
      m 0 - (J.card:ℝ)*m 1
    have hm' : (fun j : Fin (n+1) => m j.succ) (Fin.last n) = 1 := hend
    have ht (i : Fin k) :
        (∑ a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
          (∑ v : Internal (C i), if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0) =
          if i ∉ J then m 1 else 0 := by
      by_cases hi : i ∉ J
      · simp only [hi]
        exact all_choices_total (C i) _ hm'
      · simp only [hi, ite_false, Finset.sum_const_zero, zero_add]
    calc
      _ = m 0 - (k:ℝ)*m 1 + ∑ i, (
          (∑ a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
          (∑ v : Internal (C i), if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0)) := by
        rw [Finset.sum_add_distrib]; ring
      _ = m 0 - (k:ℝ)*m 1 + ∑ i : Fin k, if i ∉ J then m 1 else 0 := by simp_rw [ht]
      _ = _ := by
        rw [← Finset.sum_filter]
        have hset : Finset.univ.filter (fun i : Fin k => i ∉ J) = Finset.univ \ J := by ext i; simp
        rw [hset, Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff, Finset.inter_univ,
          Nat.cast_sub (Finset.card_le_card (Finset.subset_univ J))]
        simp only [Finset.card_univ, Fintype.card_fin]
        ring
  | @descend n k C i D ih =>
    change (∑ a : (j : Fin k) × Leaf (C j), _) +
      (∑ v : Option ((j : Fin k) × Internal (C j)), _) = _
    rw [Fintype.sum_sigma, Fintype.sum_option, Fintype.sum_sigma]
    have ho_def (j : Fin k) (a : Leaf (C j)) :
        (Divergence.descend i D).oldAllowed (⟨j,a⟩ : Leaf (.node k C)) ↔
          ∃ h : j = i, D.oldAllowed (h ▸ a) := by
      erw [Divergence.oldAllowed.eq_2]
    simp_rw [ho_def]
    simp! only [Divergence.freshAllowed, Divergence.coefficient, gamma, ite_false]
    change (∑ j, ∑ a : Leaf (C j), if ∃ h : j = i, D.oldAllowed (h ▸ a) then (1:ℝ) else 0) +
      (0 + ∑ j, ∑ v : Internal (C j), if ∃ h : j = i, D.freshAllowed (h ▸ v) then
        gamma (C j) (fun q => m q.succ) v else 0) = D.coefficient (fun q => m q.succ)
    rw [zero_add]
    have ho (j : Fin k) :
        (∑ a : Leaf (C j), if ∃ h : j = i, D.oldAllowed (h ▸ a) then (1:ℝ) else 0) =
          if j = i then (∑ a : Leaf (C i), if D.oldAllowed a then (1:ℝ) else 0) else 0 := by
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    have hf (j : Fin k) :
        (∑ v : Internal (C j), if ∃ h : j = i, D.freshAllowed (h ▸ v) then
          gamma (C j) (fun q => m q.succ) v else 0) =
          if j = i then (∑ v : Internal (C i), if D.freshAllowed v then
            gamma (C i) (fun q => m q.succ) v else 0) else 0 := by
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    simp_rw [ho, hf]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact ih _ hend

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem splitDepth_cast {n : ℕ} (A B : PrescribedTree n) (h : B = A) (a b : Leaf A) :
    splitDepth B (cast (congrArg Leaf h.symm) a) (cast (congrArg Leaf h.symm) b) =
      splitDepth A a b := by
  subst B
  rfl

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_1
/-- Fresh splitting refers to the enlarged tree's actual labeled positions. -/
theorem splitDepth_new_old {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    splitDepth (grow S v) (newLeaf S v) (oldLeaf S v a) = freshSplitDepth S v a := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (if h : (0 : Fin (k+1)) = a.1.succ then _ else 0) = 0
      rw [dite_eq_right (Ne.symm (Fin.succ_ne_zero a.1))]
    | some v =>
      obtain ⟨i,v⟩ := v
      obtain ⟨j,a⟩ := a
      by_cases h : j = i
      · subst j
        let C' := Function.update C i (grow (C i) v)
        have heq : C' i = grow (C i) v := Function.update_self ..
        have hc := splitDepth_cast (grow (C i) v) (C' i) heq
          (newLeaf (C i) v) (oldLeaf (C i) v a)
        erw [newLeaf.eq_1, oldLeaf.eq_1]
        dsimp only [id]
        simp only [dite_eq_left]
        change (if h : i = i then 1 + splitDepth (C' i)
          (cast (congrArg Leaf heq.symm) (newLeaf (C i) v))
          (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v a)) else 0) =
          (if h : i = i then 1 + freshSplitDepth (C i) v a else 0)
        simp only
        rw [hc, ih]
      · erw [newLeaf.eq_1, oldLeaf.eq_1]
        dsimp only [id]
        simp only [dite_eq_right h]
        change (if h' : i = j then _ else 0) = (if h' : j = i then _ else 0)
        rw [dite_eq_right (Ne.symm h), dite_eq_right h]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_3
theorem freshSplitDepth_same_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (v : Internal (C i)) (a : Leaf (C i)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) ⟨i,a⟩ = 1 + freshSplitDepth (C i) v a := by
  change (if h : i = i then 1 + freshSplitDepth (C i) v (h ▸ a) else 0) = _
  simp

theorem freshSplitDepth_diff_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i j : Fin k) (hij : j ≠ i) (v : Internal (C i)) (a : Leaf (C j)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) ⟨j,a⟩ = 0 := by
  change (if h : j = i then 1 + freshSplitDepth (C i) v (h ▸ a) else 0) = 0
  rw [dite_eq_right hij]

theorem freshSplitDepth_node_zero {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (v : Internal (C i)) (a : Leaf (.node k C)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) a = 0 ↔ a.1 ≠ i := by
  obtain ⟨j,a⟩ := a
  by_cases h : j = i
  · subst j
    rw [freshSplitDepth_same_child]
    simp
  · rw [freshSplitDepth_diff_child C i j h]
    simp [h]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

noncomputable local instance instDecidable_4_re2943d_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Old leaves retain their pairwise positional ancestry under actual grow. -/
theorem splitDepth_old_old {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a b : Leaf S) :
    splitDepth (grow S v) (oldLeaf S v a) (oldLeaf S v b) = splitDepth S a b := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    obtain ⟨j,a⟩ := a
    obtain ⟨l,b⟩ := b
    cases v with
    | none =>
      let D : Fin ((k+1 : ℕ+) : ℕ) → PrescribedTree n := Fin.cases (single n) C
      change splitDepth (.node (k+1) D) ⟨j.succ,a⟩ ⟨l.succ,b⟩ =
        splitDepth (.node k C) ⟨j,a⟩ ⟨l,b⟩
      by_cases h : j = l
      · subst l
        exact (@splitDepth_same_child n (k+1) D j.succ a b).trans
          (splitDepth_same_child C j a b).symm
      · exact (@splitDepth_diff_child n (k+1) D j.succ l.succ
          (fun he => h (Fin.succ_inj.mp he)) a b).trans
          (splitDepth_diff_child C j l h a b).symm
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      by_cases hjl : j = l
      · subst l
        rw [splitDepth_same_child]
        by_cases hji : j = i
        · subst j
          have heq : C' i = grow (C i) v := Function.update_self ..
          have hc := splitDepth_cast (grow (C i) v) (C' i) heq
            (oldLeaf (C i) v a) (oldLeaf (C i) v b)
          erw [oldLeaf.eq_1, oldLeaf.eq_1]
          dsimp only [id]
          simp only [dite_eq_left]
          change (if h : i = i then 1 + splitDepth (C' i)
            (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v a))
            (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v b)) else 0) = _
          simp only [dite_eq_left, hc, ih]
        · have heq : C' j = C j := Function.update_of_ne hji ..
          have hc := splitDepth_cast (C j) (C' j) heq a b
          erw [oldLeaf.eq_1, oldLeaf.eq_1]
          dsimp only [id]
          simp only [dite_eq_right hji]
          change (if h : j = j then 1 + splitDepth (C' j)
            (cast (congrArg Leaf heq.symm) a)
            (cast (congrArg Leaf heq.symm) b) else 0) = _
          simp only [dite_eq_left, hc]
      · rw [splitDepth_diff_child C j l hjl]
        apply (splitDepth_node_zero C' _ _).mpr
        change j ≠ l
        exact hjl

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem splitDepth_symm {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) :
    splitDepth S a b = splitDepth S b a := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases h : i = j
    · subst j
      rw [splitDepth_same_child, splitDepth_same_child, ih]
    · rw [splitDepth_diff_child C i j h, splitDepth_diff_child C j i (Ne.symm h)]

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_10
theorem leaves_pos {n : ℕ} (S : PrescribedTree n) : 0 < leaves S := by
  induction S with
  | leaf => decide
  | @node n k C ih =>
    exact Finset.sum_pos (fun i _ => ih i) Finset.univ_nonempty

/-- One fresh growth creates at most one branching vertex; new continuations
are unary. This holds even at coincident depths elsewhere in the tree. -/
theorem branchingCount_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (P : ℕ → Prop) :
    branchingCount (grow S v) P = branchingCount S P +
      (if P (vertexDepth S v) ∧ vertexArity S v = 1 then 1 else 0) := by
  classical
  induction S generalizing P with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (if P 0 ∧ 1 < (k:ℕ)+1 then 1 else 0) +
        (∑ j : Fin ((k:ℕ)+1), branchingCount (Fin.cases (single n) C j) (fun d => P (d+1))) =
        ((if P 0 ∧ 1 < (k:ℕ) then 1 else 0) +
          ∑ j : Fin k, branchingCount (C j) (fun d => P (d+1))) +
            (if P 0 ∧ (k:ℕ)=1 then 1 else 0)
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, branchingCount_single, zero_add]
      have hk : 0 < (k:ℕ) := k.property
      by_cases hP : P 0 <;> by_cases hk1 : (k:ℕ) = 1 <;>
        simp [hP, hk1, show ¬1 < (k:ℕ) ↔ (k:ℕ)=1 by omega, Nat.add_comm]
    | some v =>
      obtain ⟨i,v⟩ := v
      simp only [grow, branchingCount, vertexDepth, vertexArity]
      have hsum : (∑ j, branchingCount (Function.update C i (grow (C i) v) j)
          (fun d => P (d+1))) =
          (∑ j, branchingCount (C j) (fun d => P (d+1))) +
            (if P (vertexDepth (C i) v + 1) ∧ vertexArity (C i) v = 1 then 1 else 0) := by
        calc
          _ = ∑ j, (branchingCount (C j) (fun d => P (d+1)) +
                if j = i then
                  (if P (vertexDepth (C i) v + 1) ∧ vertexArity (C i) v = 1 then 1 else 0)
                else 0) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hji : j = i
              · subst j
                simp only [Function.update_self, ite_true]
                exact ih i v (fun d => P (d+1))
              · simp [hji]
          _ = _ := by simp [Finset.sum_add_distrib]
      rw [hsum, Nat.add_assoc]

theorem depthCount_le_leaves {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    depthCount S d ≤ leaves S := by
  induction S generalizing d with
  | leaf => simp [depthCount, leaves]
  | @node n k C ih =>
    cases d with
    | zero => exact leaves_pos (.node k C)
    | succ d => exact Finset.sum_le_sum (fun i _ => ih i d)

/-- Identification with the actual finite internal-vertex index type. -/
theorem depthCount_eq_sum {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    (∑ v : Internal S, if vertexDepth S v = d then (1:ℕ) else 0) = depthCount S d := by
  classical
  induction S generalizing d with
  | leaf => exact Finset.sum_eq_zero (fun v _ => nomatch v)
  | @node n k C ih =>
    change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    rw [Fintype.sum_option, Fintype.sum_sigma]
    cases d with
    | zero => simp [vertexDepth, depthCount]
    | succ d => simpa [vertexDepth, depthCount] using congrArg (Finset.sum Finset.univ) (funext (fun i => ih i d))

theorem gamma_grid_unary {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (d L : ℕ) (hv : vertexArity S v = 1) :
    gamma S (grid n d L) v = -(L:ℝ)⁻¹ := by
  induction S generalizing d with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (k:ℕ) = 1 at hv
      simp [gamma, grid, hv, Nat.cast_add, Nat.cast_one, add_div]
    | some v =>
      obtain ⟨i,v⟩ := v
      change gamma (C i) (fun j => grid (n+1) d L j.succ) v = _
      have heq : (fun j : Fin (n+1) => grid (n+1) d L j.succ) = grid n (d+1) L := by
        funext j
        simp [grid, Fin.val_succ, Nat.add_comm, Nat.add_left_comm]
      rw [heq]
      exact ih i v (d+1) hv

/-- The sum of coefficients of unary splits at a specified depth is at most
`leaves/L`, uniformly in the total number of levels. -/
theorem unary_depth_budget {n : ℕ} (S : PrescribedTree n) (d L q : ℕ) :
    (∑ v : Internal S, if vertexDepth S v = q ∧ vertexArity S v = 1 then
      |gamma S (grid n d L) v| else 0) ≤ (leaves S:ℝ) * (L:ℝ)⁻¹ := by
  classical
  calc
    _ ≤ ∑ v : Internal S, (if vertexDepth S v = q then (1:ℝ) else 0) * (L:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : vertexDepth S v = q ∧ vertexArity S v = 1
      · rw [ite_eq_left hv, gamma_grid_unary S v d L hv.2, abs_neg,
          abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), ite_eq_left hv.1, one_mul]
      · rw [ite_eq_right hv]
        positivity
    _ = (depthCount S q:ℝ) * (L:ℝ)⁻¹ := by
      rw [← Finset.sum_mul, ← depthCount_eq_sum S q]
      push_cast
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast depthCount_le_leaves S q)
      (inv_nonneg.mpr (Nat.cast_nonneg _))

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_11
theorem unary_set_budget {n : ℕ} (S : PrescribedTree n) (d L : ℕ) (Q : Finset ℕ) :
    (∑ v : Internal S, if charged S Q v then |gamma S (grid n d L) v| else 0) ≤
      (Q.card:ℝ) * (leaves S:ℝ) * (L:ℝ)⁻¹ := by
  classical
  calc
    _ = ∑ q ∈ Q, ∑ v : Internal S,
        if vertexDepth S v = q ∧ vertexArity S v = 1 then
          |gamma S (grid n d L) v| else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      by_cases ha : vertexArity S v = 1
      · simp [charged, ha]
      · simp [charged, ha]
    _ ≤ ∑ _q ∈ Q, (leaves S:ℝ) * (L:ℝ)⁻¹ :=
      Finset.sum_le_sum (fun q _ => unary_depth_budget S d L q)
    _ = _ := by simp [mul_assoc]

theorem sum_abs_gamma_grid {L : ℕ} (hL : 0 < L) (S : PrescribedTree L) :
    (∑ v : Internal S, |gamma S (grid L 0 L) v|) = (leaves S:ℝ) := by
  apply sum_abs_gamma
  · intro i j hij
    simp only [grid, Nat.zero_add]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp [grid]
  · simp [grid, ne_of_gt hL]

/-- Exact correspondence between charging steps and actual terminal branching
vertices. Distinct vertices at the same depth are counted separately. -/
theorem chargeMass_eq_historyMass {L : ℕ} (Q : Finset ℕ) (B k a : ℕ)
    (S : PrescribedTree L) :
    chargeMass Q k S a (B - branchingCount S (· ∈ Q)) =
      historyMass (fun T => if B ≤ branchingCount T (· ∈ Q) then 1 else 0) k S a := by
  classical
  induction k generalizing S a with
  | zero => simp [chargeMass, historyMass, Nat.sub_eq_zero_iff_le]
  | succ k ih =>
    simp only [chargeMass, historyMass, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    have heq : B - branchingCount (grow S v) (· ∈ Q) =
        B - branchingCount S (· ∈ Q) - (if charged S Q v then 1 else 0) := by
      rw [branchingCount_grow, Nat.sub_add_eq]
      by_cases hh : charged S Q v
      · have h := hh
        simp only [charged] at h
        simp [h, hh]
      · have h : ¬ (vertexDepth S v ∈ Q ∧ vertexArity S v = 1) := hh
        simp [h, hh]
    rw [← heq, ih]

theorem chargeBound_nonneg {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (k b : ℕ) :
    0 ≤ chargeBound C D k b := by
  induction k generalizing b with
  | zero => simp only [chargeBound]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero => exact mul_nonneg hC (ih 0)
    | succ b => exact add_nonneg (mul_nonneg hC (ih _)) (mul_nonneg hD (ih _))

/-- Every specified split contributes one factor delta; constants are independent
of the grid denominator. This also handles arbitrarily repeated target depths. -/
theorem chargeBound_scale (C D δ : ℝ) (k b : ℕ) :
    chargeBound C (D*δ) k b = chargeBound C D k b * δ^b := by
  induction k generalizing b with
  | zero =>
    cases b <;> simp [chargeBound]
  | succ k ih =>
    cases b with
    | zero => simp only [chargeBound, ih, pow_zero, mul_one]
    | succ b => simp only [chargeBound, ih, pow_succ]; ring

/-- A genuine history estimate, not a distribution postulated from the desired
identity. R bounds the leaves during all the remaining growth steps. -/
theorem chargeMass_bound {L : ℕ} (hL : 0 < L) (Q : Finset ℕ) (R k b a : ℕ)
    (S : PrescribedTree L) (ha : a ≤ leaves S) (hR : leaves S + k ≤ R) :
    chargeMass Q k S a b ≤
      chargeBound (2*(R:ℝ)) ((Q.card:ℝ)*(R:ℝ)*(L:ℝ)⁻¹) k b := by
  classical
  let C : ℝ := 2*(R:ℝ)
  let D : ℝ := (Q.card:ℝ)*(R:ℝ)*(L:ℝ)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  change chargeMass Q k S a b ≤ chargeBound C D k b
  induction k generalizing S a b with
  | zero => rfl
  | succ k ih =>
    have ho := fun b => ih b (a-1) S (Nat.le_trans (Nat.sub_le _ _) ha) (by omega)
    have hf := fun b (v : Internal S) => ih b a (grow S v) (by rw [leaves_grow]; omega)
      (by rw [leaves_grow]; omega)
    have hle : (leaves S:ℝ) ≤ (R:ℝ) := by exact_mod_cast (show leaves S ≤ R by omega)
    have haR : (a:ℝ) + (leaves S:ℝ) ≤ C := by
      have haa : (a:ℝ) ≤ (leaves S:ℝ) := by exact_mod_cast ha
      dsimp [C]
      linarith
    have hsum := sum_abs_gamma_grid hL S
    have hgood : (∑ v : Internal S, if charged S Q v then
        |gamma S (grid L 0 L) v| else 0) ≤ D :=
      (unary_set_budget S 0 L Q).trans (by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _))
    cases b with
    | zero =>
      simp only [chargeMass, Nat.zero_sub, chargeBound]
      calc
        _ ≤ (a:ℝ) * chargeBound C D k 0 +
            ∑ v : Internal S, |gamma S (grid L 0 L) v| * chargeBound C D k 0 := by
          apply add_le_add (mul_le_mul_of_nonneg_left (ho 0) (Nat.cast_nonneg _))
          exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hf 0 v) (abs_nonneg _))
        _ = ((a:ℝ)+(leaves S:ℝ))*chargeBound C D k 0 := by
          rw [← Finset.sum_mul, hsum]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right haR (chargeBound_nonneg hC hD _ _)
    | succ b =>
      have hf' (v : Internal S) :
          chargeMass Q k (grow S v) a (b+1 - if charged S Q v then 1 else 0) ≤
            chargeBound C D k (b+1) +
              (if charged S Q v then chargeBound C D k b else 0) := by
        by_cases hv : charged S Q v
        · simp only [ite_eq_left hv, Nat.add_sub_cancel]
          exact (hf b v).trans (le_add_of_nonneg_left (chargeBound_nonneg hC hD _ _))
        · simp only [ite_eq_right hv, Nat.sub_zero, add_zero]
          exact hf (b+1) v
      change (a:ℝ)*chargeMass Q k S (a-1) (b+1) + _ ≤
        C*chargeBound C D k (b+1) + D*chargeBound C D k b
      calc
        _ ≤ (a:ℝ) * chargeBound C D k (b+1) +
            ∑ v : Internal S, |gamma S (grid L 0 L) v| *
              (chargeBound C D k (b+1) +
                if charged S Q v then chargeBound C D k b else 0) := by
          exact add_le_add (mul_le_mul_of_nonneg_left (ho _) (Nat.cast_nonneg _))
            (Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hf' v) (abs_nonneg _)))
        _ = ((a:ℝ)+(leaves S:ℝ))*chargeBound C D k (b+1) +
            (∑ v : Internal S, if charged S Q v then
              |gamma S (grid L 0 L) v| else 0) * chargeBound C D k b := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
          rw [Finset.sum_mul]
          have heq : (∑ v : Internal S, |gamma S (grid L 0 L) v| *
              (if charged S Q v then chargeBound C D k b else 0)) =
              ∑ v : Internal S, (if charged S Q v then |gamma S (grid L 0 L) v| else 0) *
                chargeBound C D k b := by
            apply Finset.sum_congr rfl
            intro v _
            split <;> simp_all only [mul_zero, zero_mul]
          rw [heq]
          ring
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_right haR (chargeBound_nonneg hC hD _ _))
          (mul_le_mul_of_nonneg_right hgood (chargeBound_nonneg hC hD _ _))

 
theorem charging_final_shape {L : ℕ} (hL : 0 < L) (Q : Finset ℕ) (k b a : ℕ)
    (S : PrescribedTree L) (ha : a ≤ leaves S) :
    historyMass (fun T => if branchingCount S (· ∈ Q) + b ≤
        branchingCount T (· ∈ Q) then 1 else 0) k S a ≤
      chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k b *
        (L:ℝ)⁻¹^b := by
  rw [← chargeMass_eq_historyMass Q, Nat.add_sub_cancel_left]
  have hh := chargeMass_bound hL Q (leaves S+k) k b a S ha le_rfl
  rw [chargeBound_scale] at hh
  exact hh

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FinitePiInjective
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι κ : Type*} {α : κ → Type*}

attribute [local instance] OAI.DilutedSpinGlass.FiniteLaw.instDecidable
lemma injectionFactor_apply (e : ι → κ) (he : Function.Injective e)
    (g : (i : ι) → α (e i) → ℝ) (i : ι) (x : α (e i)) :
    injectionFactor e g (e i) x = g i x := by
  classical
  unfold injectionFactor
  have h : ∃ j, e j = e i := ⟨i,rfl⟩
  rw [dite_eq_left h]
  have ht : ∀ (j : ι) (hj : e j = e i), g j (hj.symm ▸ x) = g i x := by
    intro j hj
    have hji := he hj
    subst j
    rfl
  exact ht _ (Classical.choose_spec h)

lemma injectionFactor_outside (e : ι → κ) (g : (i : ι) → α (e i) → ℝ)
    (j : κ) (h : j ∉ Set.range e) (x : α j) : injectionFactor e g j x = 1 := by
  classical
  exact dite_eq_right h

variable [Fintype ι] [Fintype κ] [DecidableEq κ] [∀ i, Fintype (α i)]

/-- A finite family of distinct child coordinates has the corresponding
product law, regardless of the unused coordinates in the full old tree. -/
lemma expect_pi_injective_product (P : (j : κ) → FiniteLaw (α j))
    (e : ι → κ) (he : Function.Injective e) (g : (i : ι) → α (e i) → ℝ) :
    (pi P).expect (fun x => ∏ i, g i (x (e i))) = ∏ i, (P (e i)).expect (g i) := by
  have hx (x : (j : κ) → α j) : (∏ i, g i (x (e i))) =
      ∏ j, injectionFactor e g j (x j) :=
    Fintype.prod_of_injective e he _ _ (fun j hj => injectionFactor_outside e g j hj (x j))
      (fun i => (injectionFactor_apply e he g i (x (e i))).symm)
  rw [(pi P).expect_congr hx,expect_pi_product]
  symm
  apply Fintype.prod_of_injective e he
  · intro j hj
    exact ((P j).expect_congr (fun x => injectionFactor_outside e g j hj x)).trans
      ((P j).expect_const 1)
  · intro i
    exact (P (e i)).expect_congr (fun x => (injectionFactor_apply e he g i x).symm)

lemma product_point_indicator {β : ι → Type*} (x y : (i : ι) → β i) :
    (∏ i, (if x i = y i then (1:ℝ) else 0)) = (if x = y then 1 else 0) := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hh
      exact h (funext (fun i => not_not.mp (not_exists.mp hh i)))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma finite_indicator_expansion {β : ι → Type*} [∀ i, Fintype (β i)]
    (H : ((i : ι) → β i) → ℝ) (x : (i : ι) → β i) :
    H x = ∑ y, H y * ∏ i, (if x i = y i then (1:ℝ) else 0) := by
  classical
  simp_rw [product_point_indicator]
  simp

variable [DecidableEq ι]

lemma expect_pi_injective (P : (j : κ) → FiniteLaw (α j))
    (e : ι → κ) (he : Function.Injective e) (H : ((i : ι) → α (e i)) → ℝ) :
    (pi P).expect (fun x => H (fun i => x (e i))) = (pi (fun i => P (e i))).expect H := by
  classical
  have hl : (pi P).expect (fun x => H (fun i => x (e i))) =
      ∑ y, H y * ∏ i, (P (e i)).expect (fun x => if x = y i then (1:ℝ) else 0) := by
    rw [(pi P).expect_congr (fun x => finite_indicator_expansion H (fun i => x (e i)))]
    simp only [expect_fintype_sum,expect_mul_left]
    apply Finset.sum_congr (by ext; simp)
    intro y _
    exact congrArg (H y * ·) (expect_pi_injective_product P e he
      (fun i x => if x = y i then (1:ℝ) else 0))
  have hr : (pi (fun i => P (e i))).expect H =
      ∑ y, H y * ∏ i, (P (e i)).expect (fun x => if x = y i then (1:ℝ) else 0) := by
    rw [(pi (fun i => P (e i))).expect_congr (finite_indicator_expansion H)]
    simp only [expect_fintype_sum,expect_mul_left]
    apply Finset.sum_congr (by ext; simp)
    intro y _
    exact congrArg (H y * ·) (expect_pi_product (fun i => P (e i))
      (fun i x => if x = y i then (1:ℝ) else 0))
  exact hl.trans hr.symm

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeMarkLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

noncomputable local instance treeMarkLawPropDecidable_re2943d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- Deleting a newly sampled branch preserves the joint law of ALL old paths.
The old test may be arbitrarily correlated with any retained old prefixes. -/
theorem grow_projectivity {n : ℕ} (S : PrescribedTree n) (K : KernelTower Ω n)
    (v : Internal S) (H : Sample Ω S → ℝ) :
    (sampleLaw (grow S v) K).expect (fun x => H (oldSample S v x)) =
      (sampleLaw S K).expect H := by
  simpa only [mul_one,freshEval_const] using
    extension_sampling S K v H (fun _ => (1:ℝ))


end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeEmbedding
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Every old leaf of a prescribed tree has exactly the full kernel path law. -/
theorem leaf_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a : S.Leaf) (D : FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => D (S.pathAt a x)) = (KernelTower.law n T).expect D := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    change (FiniteLaw.pi (fun j => μ.bind (fun z => sampleLaw (C j) (K z)))).expect
      (fun x => D ((x i).1,(C i).pathAt a (x i).2)) = _
    have e := FiniteLaw.expect_pi_marginal
      (fun j => μ.bind (fun z => sampleLaw (C j) (K z))) i
      (fun y => D (y.1,(C i).pathAt a y.2))
    refine e.trans ?_
    erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect]
    apply FiniteLaw.expect_congr
    intro z
    exact ih i (K z) a (fun y => D (z,y))

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

namespace SplitMap
variable {n : ℕ} {T S : PrescribedTree n}

variable {k l : ℕ+} {C : Fin k → PrescribedTree n} {D : Fin l → PrescribedTree n}

lemma childIndex_injective (f : SplitMap (.node k C) (.node l D)) :
    Function.Injective f.childIndex := by
  intro i j hij
  by_contra h
  have hz : splitDepth (.node l D) (f.leaf ⟨i,firstLeaf (C i)⟩)
      (f.leaf ⟨j,firstLeaf (C j)⟩) = 0 := by
    exact (f.split ⟨i,firstLeaf (C i)⟩ ⟨j,firstLeaf (C j)⟩).trans
      (splitDepth_diff_child C i j h _ _)
  exact (splitDepth_node_zero D _ _).mp hz hij

lemma arity_le (f : SplitMap (.node k C) (.node l D)) : (k:ℕ) ≤ l := by
  have h := Fintype.card_le_of_injective _ f.childIndex_injective
  simpa only [Fintype.card_fin] using h

/-- Exact split constraints force every target branching vertex to occur in
the actual history, even when several different vertices have equal depths. -/
theorem branchingCount_le {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (P : ℕ → Prop) : branchingCount T P ≤ branchingCount S P := by
  classical
  induction T generalizing P with
  | leaf => cases S; exact le_rfl
  | @node n k C ih =>
    cases S with
    | node l D =>
      change (if P 0 ∧ 1 < (k:ℕ) then 1 else 0) +
        (∑ i, branchingCount (C i) (fun d => P (d+1))) ≤
        (if P 0 ∧ 1 < (l:ℕ) then 1 else 0) +
        (∑ j, branchingCount (D j) (fun d => P (d+1)))
      apply Nat.add_le_add
      · split_ifs with hk hl hl
        · exact le_rfl
        · exact False.elim (hl ⟨hk.1,hk.2.trans_le f.arity_le⟩)
        · exact Nat.zero_le _
        · exact le_rfl
      · calc
          _ ≤ ∑ i, branchingCount (D (f.childIndex i)) (fun d => P (d+1)) :=
            Finset.sum_le_sum (fun i _ => ih i (f.child i) (fun d => P (d+1)))
          _ = ∑ j ∈ Finset.univ.image f.childIndex, branchingCount (D j) (fun d => P (d+1)) := by
            rw [Finset.sum_image]
            exact fun i _ j _ h => f.childIndex_injective h
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)

end SplitMap
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_LabeledColorHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

lemma expect_pi_pair (P : (i : ι) → FiniteLaw (α i)) (i j : ι) (hij : j ≠ i)
    (f : α i → α j → ℝ) :
    (pi P).expect (fun x => f (x i) (x j)) =
      (P i).expect (fun x => (P j).expect (f x)) := by
  rw [expect_pi_split P i]
  apply expect_congr
  intro x
  simp only [Equiv.piSplitAt_symm_apply,dite_true,dite_eq_right hij]
  exact expect_pi_marginal (fun k : {k // k ≠ i} => P k) ⟨j,hij⟩ (f x)

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- The complete TWO-path joint law is determined by geometric splitting,
not by coincidences of configurations. Unused branches are marginalized. -/
theorem pair_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (f : FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x) (S.pathAt b x)) =
      KernelTower.pairExpect n T (splitDepth S a b) f := by
  induction S with
  | leaf =>
    change KernelTower.unitLaw.expect (fun _ => f () ()) = f () ()
    exact FiniteLaw.expect_const _ _
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    by_cases hji : j = i
    · subst j
      rw [splitDepth_same_child]
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => f ((x i).1,(C i).pathAt a (x i).2) ((x i).1,(C i).pathAt b (x i).2)) = _
      refine (FiniteLaw.expect_pi_marginal
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i
        (fun x => f (x.1,(C i).pathAt a x.2) (x.1,(C i).pathAt b x.2))).trans ?_
      erw [FiniteLaw.expect_bind]
      simp only [Nat.add_comm 1,KernelTower.pairExpect]
      apply FiniteLaw.expect_congr
      intro z
      exact ih i (K z) a b (fun x y => f (z,x) (z,y))
    · rw [splitDepth_diff_child C i j (Ne.symm hji)]
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => f ((x i).1,(C i).pathAt a (x i).2) ((x j).1,(C j).pathAt b (x j).2)) = _
      refine (FiniteLaw.expect_pi_pair
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i j hji
        (fun x y => f (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2))).trans ?_
      erw [FiniteLaw.expect_bind]
      simp only [FiniteLaw.expect_bind,KernelTower.pairExpect]
      erw [KernelTower.law_succ_expect n (μ,K)]
      simp_rw [KernelTower.law_succ_expect n (μ,K)]
      apply FiniteLaw.expect_congr
      intro x
      rw [← leaf_marginal (C i) (K x) a]
      apply FiniteLaw.expect_congr
      intro y
      apply FiniteLaw.expect_congr
      intro z
      exact leaf_marginal (C j) (K z) b (fun w => f (x,(C i).pathAt a y) (z,w))

lemma pair_marginal_eq {n : ℕ} (S R : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (c d : R.Leaf) (h : splitDepth S a b = splitDepth R c d)
    (f : FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x) (S.pathAt b x)) =
      (R.sampleLaw T).expect (fun x => f (R.pathAt c x) (R.pathAt d x)) := by
  rw [pair_marginal,pair_marginal,h]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SplitDepthContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidableSplitDepthContinuity
lemma pairDivergence_coefficient {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    (pairDivergence S a d hd).coefficient m =
      m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩ := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero => simp [pairDivergence,Divergence.coefficient]
    | succ d => exact ih a.1 a.2 d (by omega) (fun j => m j.succ)

lemma pairDivergence_old {n : ℕ} (S : PrescribedTree n) (a b : S.Leaf)
    (d : ℕ) (hd : d < n) :
    (pairDivergence S a d hd).oldAllowed b ↔ splitDepth S a b = d := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    cases d with
    | zero =>
      change j ∉ ({i} : Finset (Fin k)) ↔ _
      simp only [Finset.mem_singleton]
      by_cases h : i = j
      · subst j; rw [splitDepth_same_child]; simp
      · rw [splitDepth_diff_child C i j h]; simp [Ne.symm h]
    | succ d =>
      change (∃ h : j = i, (pairDivergence (C i) a d (by omega)).oldAllowed (h ▸ b)) ↔ _
      by_cases h : j = i
      · subst j
        simp only [exists_const,splitDepth_same_child]
        rw [ih i a b d (by omega)]
        omega
      · rw [splitDepth_diff_child C i j (Ne.symm h)]
        constructor
        · rintro ⟨he,_⟩; exact (h he).elim
        · intro he; omega

lemma pairDivergence_fresh {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (v : S.Internal) (d : ℕ) (hd : d < n) :
    (pairDivergence S a d hd).freshAllowed v ↔ freshSplitDepth S v a = d := by
  induction S generalizing d with
  | leaf => exact v.elim
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    change Option ((j : Fin k) × (C j).Internal) at v
    cases d with
    | zero =>
      cases v with
      | none => change True ↔ 0 = 0; simp
      | some v =>
        rcases v with ⟨j,v⟩
        change j ∉ ({i} : Finset (Fin k)) ↔ _
        simp only [Finset.mem_singleton]
        exact ne_comm.trans (freshSplitDepth_node_zero C j v ⟨i,a⟩).symm
    | succ d =>
      cases v with
      | none => change False ↔ 0 = d+1; simp
      | some v =>
        rcases v with ⟨j,v⟩
        change (∃ h : j = i, (pairDivergence (C i) a d (by omega)).freshAllowed (h ▸ v)) ↔ _
        by_cases h : j = i
        · subst j
          simp only [exists_const,freshSplitDepth_same_child]
          rw [ih i a v d (by omega)]
          omega
        · rw [freshSplitDepth_diff_child C j i (Ne.symm h)]
          constructor
          · rintro ⟨he,_⟩; exact (h he).elim
          · intro he; omega

/-- Exact signed total of every path splitting from the anchor at d. -/
theorem pair_choice_total {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0) +
      (∑ v : S.Internal, if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d
        then gamma S m v else 0) = m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩ := by
  simp_rw [splitDepth_symm (grow S _) (oldLeaf S _ a),splitDepth_new_old,
    ← pairDivergence_old S a _ d hd,← pairDivergence_fresh S a _ d hd]
  rw [divergence_choice_total _ m hend,pairDivergence_coefficient]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree.SplitMap
open scoped BigOperators
variable {Ω : Type}

lemma pathAt_pullSample {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (a : T.Leaf) (x : Sample Ω S) :
    T.pathAt a (f.pullSample x) = S.pathAt (f.leaf a) x := by
  induction T with
  | leaf => cases S; rfl
  | @node n k C ih =>
    cases S with
    | node l D =>
      rcases a with ⟨i,a⟩
      rw [f.leaf_eq_child i a]
      change ((x (f.childIndex i)).1,pathAt (C i) a ((f.child i).pullSample (x (f.childIndex i)).2)) =
        ((x (f.childIndex i)).1,pathAt (D (f.childIndex i)) ((f.child i).leaf a) (x (f.childIndex i)).2)
      rw [ih]

variable [Fintype Ω]

/-- Every exact prescribed splitting matrix has the same sampling law in
EVERY actual extension, jointly over its entire selected leaf family. -/
theorem expect_pullSample {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (K : KernelTower Ω n) (F : Sample Ω T → ℝ) :
    (S.sampleLaw K).expect (fun x => F (f.pullSample x)) = (T.sampleLaw K).expect F := by
  classical
  induction T with
  | leaf => cases S; rfl
  | @node n k C ih =>
    cases S with
    | node l D =>
      rcases K with ⟨μ,K⟩
      let P := fun j : Fin l => μ.bind (fun z => sampleLaw (D j) (K z))
      let Q := fun i : Fin k => μ.bind (fun z => sampleLaw (C i) (K z))
      let φ := fun (i : Fin k) (x : Ω × Sample Ω (D (f.childIndex i))) =>
        (x.1,(f.child i).pullSample x.2)
      change (FiniteLaw.pi P).expect (fun x => F (fun i => φ i (x (f.childIndex i)))) =
        (FiniteLaw.pi Q).expect F
      have hp := FiniteLaw.expect_pi_injective P f.childIndex f.childIndex_injective
        (fun x => F (fun i => φ i (x i)))
      refine hp.trans ?_
      have hφ : ∀ (i : Fin k) (g : Ω × Sample Ω (C i) → ℝ),
          (P (f.childIndex i)).expect (fun x => (1:ℝ)*g (φ i x)) =
          (Q i).expect (fun y => (1:ℝ)*g y) := by
        intro i g
        simp only [one_mul,P,Q,FiniteLaw.expect_bind]
        apply FiniteLaw.expect_congr
        intro z
        exact ih i (f.child i) (K z) (fun y => g (z,y))
      simpa only [Finset.prod_const_one,mul_one] using FiniteLaw.expect_pi_weighted_map
        (fun i => P (f.childIndex i)) Q φ (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) hφ F

/-- Same joint marginal expressed directly in leaf paths, so terminal overlap
and projection-error observables can use it without any sample relabeling. -/
theorem expect_paths {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (K : KernelTower Ω n) (F : (T.Leaf → FinitePath Ω n) → ℝ) :
    (S.sampleLaw K).expect (fun x => F (fun a => S.pathAt (f.leaf a) x)) =
      (T.sampleLaw K).expect (fun x => F (fun a => T.pathAt a x)) := by
  have he := f.expect_pullSample K (fun x => F (fun a => T.pathAt a x))
  simpa only [pathAt_pullSample] using he

end DilutedSpinGlass.PrescribedTree.SplitMap
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HistorySelector
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {L : ℕ}

lemma historyMass_mul (F : PrescribedTree L → ℝ) (E : ℝ) (k : ℕ)
    (S : PrescribedTree L) (a : ℕ) :
    historyMass (fun T => E*F T) k S a = E*historyMass F k S a := by
  induction k generalizing S a with
  | zero => rfl
  | succ k ih =>
    simp only [historyMass,ih]
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro v _
      ring

variable {Ω C ι : Type} [DecidableEq C] [DecidableEq ι]

/-- Every literal labeled extension contributes its actual absolute coefficient.
The domination retains all old tests rather than replacing the sampled law by
an unsigned or independently resampled one. -/
theorem labeledHistory_abs_le_mass (F : PrescribedTree L → ℝ)
    (V : (S : PrescribedTree L) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hV : ∀ S pos f, (∀ x, |f x| ≤ 1) → |V S pos f| ≤ F S)
    (cs : List C) (S : PrescribedTree L) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |labeledHistory (grid L 0 L) V cs S U loc pos f| ≤ historyMass F cs.length S U.card := by
  induction cs generalizing S U with
  | nil => exact hV S pos f hf
  | cons c cs ih =>
    simp only [labeledHistory,List.length_cons,historyMass]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · calc
        _ ≤ ∑ i ∈ U, |labeledHistory (grid L 0 L) V cs S (U.erase i) loc
            (Function.update pos c (loc i)) f| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ U, historyMass F cs.length S (U.card-1) := by
          apply Finset.sum_le_sum
          intro i hi
          have h := ih S (U.erase i) loc (Function.update pos c (loc i)) f hf
          simpa only [Finset.card_erase_of_mem hi] using h
        _ = _ := by simp [nsmul_eq_mul]
    · calc
        _ ≤ ∑ v : S.Internal, |gamma S (grid L 0 L) v *
            labeledHistory (grid L 0 L) V cs (grow S v) U
            (fun i => oldLeaf S v (loc i))
            (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
            (fun x => f (oldSample S v x))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro v _
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact ih (grow S v) U _ _ _ (fun x => hf (oldSample S v x))

/-- Charging estimate for an actual labeled terminal observable. Restricting
the allowed splitting matrices and inserting a uniformly bounded projection
error are both handled in this single estimate. -/
theorem labeledHistory_charging_bound (hL : 0 < L) (Q : Finset ℕ) (b : ℕ)
    (V : (S : PrescribedTree L) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (E : ℝ) (hE : 0 ≤ E) (cs : List C) (S : PrescribedTree L)
    (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S)
    (hV : ∀ T pos g, (∀ x, |g x| ≤ 1) → |V T pos g| ≤ E *
      (if branchingCount S (· ∈ Q)+b ≤ branchingCount T (· ∈ Q) then 1 else 0)) :
    |labeledHistory (grid L 0 L) V cs S U loc pos f| ≤
      E * (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
        cs.length b * (L:ℝ)⁻¹^b) := by
  have h := labeledHistory_abs_le_mass
    (fun T => E*(if branchingCount S (· ∈ Q)+b ≤ branchingCount T (· ∈ Q) then 1 else 0))
    V hV cs S U loc pos f hf
  rw [historyMass_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (charging_final_shape hL Q cs.length b U.card S hU) hE)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω C : Type} [Fintype Ω] {n : ℕ}

/-- Complete positional splitting matrices determine the full joint path law,
not just pair overlaps. The enumerating colors may repeat leaf positions. -/
theorem matrix_paths_expect (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (K : KernelTower Ω n) (F : (C → FinitePath Ω n) → ℝ) :
    (S.sampleLaw K).expect (fun x => F (fun c => S.pathAt (pos c) x)) =
      (T.sampleLaw K).expect (fun x => F (fun c => T.pathAt (q c) x)) := by
  classical
  let e : SplitMap T S := {
    leaf := fun a => pos (Function.surjInv hq a)
    split := fun a b => (h _ _).trans
      (congrArg₂ (splitDepth T) (Function.surjInv_eq hq a) (Function.surjInv_eq hq b)) }
  have he (c : C) : e.leaf (q c) = pos c := by
    apply (splitDepth_eq_height S _ _).mp
    exact (h (Function.surjInv hq (q c)) c).trans
      ((congrArg (fun z => splitDepth T z (q c)) (Function.surjInv_eq hq (q c))).trans
        (splitDepth_self T (q c)))
  have hm := e.expect_paths K (fun x => F (fun c => x (q c)))
  simpa only [he] using hm

/-- An arbitrary correlated old test bounded by one costs at most the actual
single-target L2 error, since the entire target marginal is fixed. -/
theorem matrix_weighted_error (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (K : KernelTower Ω n) (D : (C → FinitePath Ω n) → ℝ)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(S.sampleLaw K).expect (fun x => f x * D (fun c => S.pathAt (pos c) x))| ≤
      (T.sampleLaw K).l2 (fun x => D (fun c => T.pathAt (q c) x)) := by
  let P := S.sampleLaw K
  let g := fun x : Sample Ω S => D (fun c => S.pathAt (pos c) x)
  have hsq := P.expect_mul_sq_le f g
  have hf2 : P.expect (fun x => f x^2) ≤ 1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        have hx : f x^2 ≤ (1:ℝ)^2 := sq_le_sq.mpr (by simpa using hf x)
        simpa using hx)
      _ = _ := P.expect_const 1
  have he : P.expect (fun x => g x^2) =
      (T.sampleLaw K).expect (fun x => D (fun c => T.pathAt (q c) x)^2) :=
    matrix_paths_expect T S q hq pos h K (fun x => D x^2)
  have hd := (T.sampleLaw K).l2_nonneg (fun x => D (fun c => T.pathAt (q c) x))
  apply (sq_le_sq₀ (abs_nonneg _) hd).mp
  rw [sq_abs,FiniteLaw.l2_sq,← he]
  exact hsq.trans (by nlinarith [P.expect_nonneg (fun x => sq_nonneg (g x))])

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {Ω C ι : Type} [Fintype C] [DecidableEq C] [DecidableEq ι] {L : ℕ}

omit [Fintype C] [DecidableEq C] in
/-- A shape specified by a complete labeled splitting matrix contains each
of the target's branching vertices, with its vertex multiplicity intact. -/
lemma branchingCount_of_matrix (T S : PrescribedTree L) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (P : ℕ → Prop) : branchingCount T P ≤ branchingCount S P := by
  classical
  let e : SplitMap T S := {
    leaf := fun a => pos (Function.surjInv hq a)
    split := fun a b => (h _ _).trans
      (congrArg₂ (splitDepth T) (Function.surjInv_eq hq a) (Function.surjInv_eq hq b)) }
  exact e.branchingCount_le P

/-- Absolute projection-error cost for the ACTUAL exact-matrix history. This
is the charging step in the shifted-two-copy argument: take Q to be shifted
depths, so the old tree has no branching in Q. The exponent counts vertices,
not distinct depths, hence aligned copies are charged separately. -/
theorem prescribed_history_charging_bound (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0)
    (W : (R : PrescribedTree L) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (E : ℝ) (hE : 0 ≤ E)
    (hW : ∀ R pos g, (∀ x, |g x| ≤ 1) →
      (∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)) → |W R pos g| ≤ E)
    (cs : List C) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then W R pos g else 0) cs S U loc pos f| ≤
      E * (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
        cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  classical
  apply labeledHistory_charging_bound hL Q (branchingCount T (· ∈ Q)) _ E hE cs S
    U loc pos f hf hU
  intro R loc g hg
  by_cases h : ∀ a b, splitDepth R (loc a) (loc b) = splitDepth T (q a) (q b)
  · rw [ite_eq_left h]
    have hc := branchingCount_of_matrix T R q hq loc h (· ∈ Q)
    rw [hS,zero_add,ite_eq_left hc,mul_one]
    exact hW R loc g hg h
  · rw [ite_eq_right h,abs_zero]
    exact mul_nonneg hE (by split_ifs <;> norm_num)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TripleMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {L : ℕ}

omit [Fintype Ω] [Fintype C] in
lemma labeledHistory_sub (m : Fin (L+1) → ℝ)
    (V W : (R : PrescribedTree L) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree L) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => V R pos g-W R pos g) cs S U loc pos f =
      labeledHistory m V cs S U loc pos f-labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [labeledHistory,ih,mul_sub,Finset.sum_sub_distrib]
    ring

/-- The genuine signed history of an L2 projection error has the exact
small-L charging cost. The target error need only be small under its own
single-copy law; it may be correlated with every old path and old test. -/
theorem projection_history_cost (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (D : (C → FinitePath Ω L) → ℝ) (cs : List C) (U : Finset ι)
    (loc : ι → S.Leaf) (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*D (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f| ≤
      (T.sampleLaw K).l2 (fun x => D (fun c => T.pathAt (q c) x)) *
        (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
          cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  refine prescribed_history_charging_bound hL Q T S q hq hS _ _
    (FiniteLaw.l2_nonneg _ _) ?_ cs U loc pos f hf hU
  intro R pos g hg h
  exact matrix_weighted_error T R q hq pos h K D g hg

/-- Direct comparison of an actual target overlap with its projected
observable inside the full signed ordered extension sum. -/
theorem projection_history_difference (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (A B : (C → FinitePath Ω L) → ℝ) (cs : List C) (U : Finset ι)
    (loc : ι → S.Leaf) (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*A (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f -
     labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*B (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f| ≤
      (T.sampleLaw K).l2 (fun x => A (fun c => T.pathAt (q c) x)-B (fun c => T.pathAt (q c) x)) *
        (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
          cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  rw [← labeledHistory_sub]
  have he : (fun (R : PrescribedTree L) (pos : C → R.Leaf) (g : Sample Ω R → ℝ) =>
      (if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*A (fun c => R.pathAt (pos c) x)) else 0)-
      (if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*B (fun c => R.pathAt (pos c) x)) else 0)) =
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*(A (fun c => R.pathAt (pos c) x)-
          B (fun c => R.pathAt (pos c) x))) else 0) := by
    funext R pos g
    split_ifs <;> simp only [sub_self,mul_sub,FiniteLaw.expect_sub]
  rw [he]
  exact projection_history_cost hL Q T S q hq hS K (fun x => A x-B x) cs U loc pos f hf hU

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
lemma expect_pi_three (P : (i : ι) → FiniteLaw (α i)) (i j k : ι)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) (f : α i → α j → α k → ℝ) :
    (pi P).expect (fun x => f (x i) (x j) (x k)) =
      (P i).expect (fun x => (P j).expect (fun y => (P k).expect (f x y))) := by
  rw [expect_pi_split P i]
  apply expect_congr
  intro x
  simp only [Equiv.piSplitAt_symm_apply,dite_true,dite_eq_right hji,dite_eq_right hki]
  exact expect_pi_pair (fun t : {t // t ≠ i} => P t) ⟨j,hji⟩ ⟨k,hki⟩
    (fun he => hkj (congrArg Subtype.val he)) (f x)
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
lemma branch_leaf_marginal {n : ℕ} (C : PrescribedTree n) (μ : FiniteLaw Ω)
    (K : Ω → KernelTower Ω n) (a : C.Leaf) (F : FinitePath Ω (n+1) → ℝ) :
    (μ.bind (fun z => C.sampleLaw (K z))).expect
      (fun x => F (x.1,C.pathAt a x.2)) = (KernelTower.law (n+1) (μ,K)).expect F := by
  erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect n (μ,K)]
  exact μ.expect_congr (fun z => leaf_marginal C (K z) a (fun y => F (z,y)))

/-- Every uncontracted tree with three positional pairwise split depths equal
to d has the genuine three-copy conditional marginal. All other branches are
integrated out, irrespective of their number or depths. -/
theorem triple_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b c : S.Leaf) (d : ℕ) (hd : d < n)
    (hab : splitDepth S a b = d) (hac : splitDepth S a c = d)
    (hbc : splitDepth S b c = d)
    (F : FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => F (S.pathAt a x) (S.pathAt b x) (S.pathAt c x)) =
      KernelTower.tripleExpectAt n T d F := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    rcases c with ⟨l,c⟩
    cases d with
    | zero =>
      have hji : j ≠ i := by
        intro hj; subst j
        rw [splitDepth_same_child] at hab
        omega
      have hli : l ≠ i := by
        intro hl; subst l
        rw [splitDepth_same_child] at hac
        omega
      have hlj : l ≠ j := by
        intro hl; subst l
        rw [splitDepth_same_child] at hbc
        omega
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => F ((x i).1,(C i).pathAt a (x i).2) ((x j).1,(C j).pathAt b (x j).2)
          ((x l).1,(C l).pathAt c (x l).2)) = _
      refine (FiniteLaw.expect_pi_three
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i j l hji hli hlj
        (fun x y z => F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2)
          (z.1,(C l).pathAt c z.2))).trans ?_
      change _ = (KernelTower.law (n+1) (μ,K)).expect (fun x =>
        (KernelTower.law (n+1) (μ,K)).expect (fun y =>
          (KernelTower.law (n+1) (μ,K)).expect (F x y)))
      calc
        _ = (μ.bind (fun z => sampleLaw (C i) (K z))).expect (fun x =>
          (μ.bind (fun z => sampleLaw (C j) (K z))).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z =>
              F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2) z))) := by
          apply FiniteLaw.expect_congr; intro x
          apply FiniteLaw.expect_congr; intro y
          exact branch_leaf_marginal (C l) μ K c
            (fun z => F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2) z)
        _ = (μ.bind (fun z => sampleLaw (C i) (K z))).expect (fun x =>
          (KernelTower.law (n+1) (μ,K)).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z => F (x.1,(C i).pathAt a x.2) y z))) := by
          apply FiniteLaw.expect_congr; intro x
          exact branch_leaf_marginal (C j) μ K b (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z => F (x.1,(C i).pathAt a x.2) y z))
        _ = _ := branch_leaf_marginal (C i) μ K a (fun x =>
          (KernelTower.law (n+1) (μ,K)).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (F x y)))
    | succ d =>
      have hji : j = i := by
        by_contra hj
        rw [splitDepth_diff_child C i j (Ne.symm hj)] at hab
        omega
      have hli : l = i := by
        by_contra hl
        rw [splitDepth_diff_child C i l (Ne.symm hl)] at hac
        omega
      subst j; subst l
      rw [splitDepth_same_child] at hab hac hbc
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => F ((x i).1,(C i).pathAt a (x i).2) ((x i).1,(C i).pathAt b (x i).2)
          ((x i).1,(C i).pathAt c (x i).2)) = _
      refine (FiniteLaw.expect_pi_marginal
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i
        (fun x => F (x.1,(C i).pathAt a x.2) (x.1,(C i).pathAt b x.2)
          (x.1,(C i).pathAt c x.2))).trans ?_
      rw [FiniteLaw.expect_bind]
      exact μ.expect_congr (fun z => ih i (K z) a b c d (by omega) (by omega) (by omega)
        (by omega) (fun x y w => F (z,x) (z,y) (z,w)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance kappaRegularDecidable_re2943d_1 (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.kappaRegularLeafDecidableEq
lemma branchProduct_ne_zero {x y : ℝ} (hxy : x < y) (hy : 0 ≤ y) (k : ℕ) :
    branchProduct x y k ≠ 0 := by
  unfold branchProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply ne_of_lt
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hmul := mul_nonneg hj hy
  nlinarith

theorem partialKappa_ne_zero {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (P : Finset S.Leaf) :
    partialKappa S m P ≠ 0 := by
  induction S with
  | leaf => exact one_ne_zero
  | @node n k C ih =>
    apply mul_ne_zero
    · exact branchProduct_ne_zero (hm (by simp : (0 : Fin (n+1+1)) < 1)) (hp 1) _
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => ih i _
        (fun a b h => hm (Fin.succ_lt_succ_iff.mpr h)) (fun j => hp j.succ) _)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_GlobalSelectedAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance pairObservableHistoryDecidable_re2943d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma pair_univ_erase (S : PrescribedTree n) (a : S.Leaf) (d : ℕ) (hd : d < n) :
    (∑ b ∈ Finset.univ.erase a, if splitDepth S a b = d then (1:ℝ) else 0) =
      ∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0 := by
  classical
  have he := Finset.sum_erase_add (Finset.univ : Finset S.Leaf)
    (fun b => if splitDepth S a b = d then (1:ℝ) else 0) (Finset.mem_univ a)
  simpa only [splitDepth_self,ite_eq_right (Ne.symm (Nat.ne_of_lt hd)),add_zero] using he

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PairSquare
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance pairSquareDecidable_re2943d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma pairFreshCost_nonneg (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (a : S.Leaf) (d : ℕ) (v : S.Internal) :
    0 ≤ pairFreshCost S m a d v := by
  unfold pairFreshCost
  split_ifs
  · exact neg_nonneg.mpr (gamma_nonpos S m hm hp v)
  · rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_GeneralPairSquare
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance generalPairSquareDecidable_re2943d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- The exact nonnegative-square identity before root averaging. It follows
from actual two-path marginals and complete old-law projectivity. -/
theorem pair_square_identity_general (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (a b : S.Leaf)
    (d : ℕ) (hd : d < n) (hsplit : splitDepth S a b = d)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ)
    (hOld : ∀ c, splitDepth S a c = d → ∀ x : Sample Ω S,
      R (S.pathAt a x) (S.pathAt c x) = R (S.pathAt a x) (S.pathAt b x)) :
    (1/2:ℝ) * ∑ v : S.Internal, pairFreshCost S m a d v *
      ((grow S v).sampleLaw T).expect (fun x =>
        (R (S.pathAt a (oldSample S v x)) (S.pathAt b (oldSample S v x)) -
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x))^2) =
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        (S.sampleLaw T).expect (fun x => R (S.pathAt a x) (S.pathAt b x)^2) +
      pairObservableHistory T m S a d R (fun x => R (S.pathAt a x) (S.pathAt b x)) := by
  classical
  let X := fun x : Sample Ω S => R (S.pathAt a x) (S.pathAt b x)
  let Y := fun (v : S.Internal) (x : Sample Ω (grow S v)) =>
    R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)
  let A := (S.sampleLaw T).expect (fun x => X x^2)
  let Q := fun v : S.Internal => ((grow S v).sampleLaw T).expect
    (fun x => X (oldSample S v x)*Y v x)
  let e := m ⟨d,by omega⟩-m ⟨d+1,by omega⟩
  let q : ℝ := ∑ c ∈ (Finset.univ : Finset S.Leaf).erase a,
    if splitDepth S a c = d then 1 else 0
  have hsum : (∑ v : S.Internal, pairFreshCost S m a d v) = q-e := by
    have hh := pair_choice_total S a d hd m hend
    rw [← pair_univ_erase S a d hd] at hh
    have hn (v : S.Internal) : pairFreshCost S m a d v =
        -(if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then gamma S m v else 0) := by
      unfold pairFreshCost; split_ifs <;> simp
    simp_rw [hn,Finset.sum_neg_distrib]
    dsimp only [e]
    linarith
  have hsq (v : S.Internal)
      (hv : splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d) :
      ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2) =
        2*A-2*Q v := by
    have hy : ((grow S v).sampleLaw T).expect (fun x => Y v x^2) = A := by
      exact pair_marginal_eq (grow S v) S T (oldLeaf S v a) (newLeaf S v) a b
        (hv.trans hsplit.symm) (fun x y => R x y^2)
    calc
      _ = ((grow S v).sampleLaw T).expect (fun x =>
        X (oldSample S v x)^2 - 2*(X (oldSample S v x)*Y v x) + Y v x^2) :=
          FiniteLaw.expect_congr _ (fun _ => by ring)
      _ = _ := by
        rw [FiniteLaw.expect_add,FiniteLaw.expect_sub,FiniteLaw.expect_mul_left,
          grow_projectivity S T v (fun x => X x^2),hy]
        change A-2*Q v+A = 2*A-2*Q v
        ring
  have hterm (v : S.Internal) : pairFreshCost S m a d v *
      ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2) =
      2*(pairFreshCost S m a d v*A) - 2*(pairFreshCost S m a d v*Q v) := by
    by_cases hv : splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d
    · rw [hsq v hv]; ring
    · simp only [pairFreshCost,hv,ite_false,zero_mul,mul_zero,sub_zero]
  have hhist : pairObservableHistory T m S a d R X = q*A - ∑ v : S.Internal,
      pairFreshCost S m a d v*Q v := by
    unfold pairObservableHistory
    have ha : (∑ c ∈ (Finset.univ : Finset S.Leaf).erase a,
        if splitDepth S a c = d then (S.sampleLaw T).expect
          (fun x => X x * R (S.pathAt a x) (S.pathAt c x)) else 0) = q*A := by
      dsimp only [q]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs with hs
      · rw [one_mul]
        apply FiniteLaw.expect_congr
        intro x
        rw [hOld c hs x]
        change X x * X x = X x^2
        ring
      · simp
    rw [ha,sub_eq_add_neg,← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    unfold pairFreshCost
    split_ifs
    · change gamma S m v * Q v = -(-gamma S m v * Q v)
      ring
    · simp
  have hminus : m ⟨d+1,by omega⟩ - m ⟨d,by omega⟩ = -e := by dsimp [e]; ring
  rw [hminus]
  change (1/2:ℝ)*(∑ v, pairFreshCost S m a d v *
    ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2)) =
    (-e)*A+pairObservableHistory T m S a d R X
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_mul,hsum,hhist]
  ring


end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type*} [Fintype Ω]
lemma abs_expect_mul_le_l2 (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (hg : ∀ x, |g x| ≤ 1) : |P.expect (fun x => f x*g x)| ≤ P.l2 f := by
  have hs := P.expect_mul_sq_le f g
  have hg2 : P.expect (fun x => g x^2) ≤ 1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        simpa using (sq_le_sq.mpr (show |g x| ≤ |(1:ℝ)| by simpa using hg x)))
      _ = _ := P.expect_const 1
  apply (sq_le_sq₀ (abs_nonneg _) (P.l2_nonneg _)).mp
  rw [sq_abs,l2_sq]
  exact hs.trans (by nlinarith [P.expect_nonneg (fun x => sq_nonneg (f x))])
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance singletonRootPropDecidable_re2943d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma grow_l2 (S : PrescribedTree n) (v : S.Internal) (K : KernelTower Ω n)
    (f : Sample Ω S → ℝ) :
    ((grow S v).sampleLaw K).l2 (fun x => f (oldSample S v x)) = (S.sampleLaw K).l2 f := by
  unfold FiniteLaw.l2
  exact congrArg Real.sqrt (grow_projectivity S K v (fun x => f x^2))

lemma pairObservableHistory_sub_test (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f g : Sample Ω S → ℝ) :
    pairObservableHistory K m S a d R (fun x => f x-g x) =
      pairObservableHistory K m S a d R f-pairObservableHistory K m S a d R g := by
  unfold pairObservableHistory
  simp only [sub_mul,FiniteLaw.expect_sub,mul_sub]
  have p (b : S.Leaf) :
      (if splitDepth S a b = d then
        (S.sampleLaw K).expect (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) -
        (S.sampleLaw K).expect (fun x => g x*R (S.pathAt a x) (S.pathAt b x)) else 0) =
      (if splitDepth S a b = d then (S.sampleLaw K).expect
        (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) else 0) -
      (if splitDepth S a b = d then (S.sampleLaw K).expect
        (fun x => g x*R (S.pathAt a x) (S.pathAt b x)) else 0) := by split_ifs <;> ring
  have q (v : S.Internal) :
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x))-
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => g (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0) =
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0)-
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => g (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0) := by split_ifs <;> ring
  simp_rw [p,q]
  simp only [Finset.sum_sub_distrib]
  ring

/-- Changing the old test has its original L2 cost, not a sup norm cost; fresh
branches preserve its entire old marginal. -/
theorem pairObservableHistory_l2 (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ)
    (hR : ∀ x y, |R x y| ≤ 1) :
    |pairObservableHistory K m S a d R f| ≤ pairHistoryMass S m a*(S.sampleLaw K).l2 f := by
  let B := (S.sampleLaw K).l2 f
  have hB : 0 ≤ B := FiniteLaw.l2_nonneg _ _
  unfold pairObservableHistory pairHistoryMass
  calc
    _ ≤ (∑ b ∈ (Finset.univ : Finset S.Leaf).erase a,
      |if splitDepth S a b = d then (S.sampleLaw K).expect (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) else 0|) +
      ∑ v : S.Internal, |if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (∑ _b ∈ (Finset.univ : Finset S.Leaf).erase a, B) + ∑ v : S.Internal, |gamma S m v| * B := by
      apply add_le_add
      · apply Finset.sum_le_sum; intro b _
        split_ifs
        · exact FiniteLaw.abs_expect_mul_le_l2 _ _ _ (fun x => hR _ _)
        · simpa using hB
      · apply Finset.sum_le_sum; intro v _
        split_ifs
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact (FiniteLaw.abs_expect_mul_le_l2 _ _ _ (fun x => hR _ _)).trans_eq (grow_l2 S v K f)
        · simpa using mul_nonneg (abs_nonneg (gamma S m v)) hB
    _ = _ := by simp [B,← Finset.sum_mul,add_mul]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
lemma abs_dot_le_one {N : ℕ} (x y : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) : |dot x y| ≤ 1 := by
  by_cases hN : N = 0
  · subst N; simp [dot]
  have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [dot,abs_div,abs_of_pos hp,div_le_iff₀ hp,one_mul]
  calc
    _ ≤ ∑ i, |x i*y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hy i))
    _ = _ := by simp
end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

noncomputable local instance matrixEnergyPropDecidable_re2943d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma grid_strictMono (hL : 0 < L) : StrictMono (grid L 0 L) := by
  intro i j hij
  dsimp only [grid]
  simp only [Nat.zero_add]
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (Nat.cast_pos.mpr hL)

lemma grid_nonneg : ∀ j, 0 ≤ grid L 0 L j := by
  intro j
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma grid_last (hL : 0 < L) : grid L 0 L (Fin.last L) = 1 := by
  simp [grid,ne_of_gt hL]

lemma signed_approximation {H HP J E : ℝ} (hJ : J ≠ 0) (h : |H-HP| ≤ E) :
    HP/J ≤ H/J+E/|J| := by
  have he : HP/J-H/J = (HP-H)/J := by ring
  have hh : HP/J-H/J ≤ E/|J| := by
    rw [he]
    calc
      _ ≤ |(HP-H)/J| := le_abs_self _
      _ = |H-HP|/|J| := by rw [abs_div,abs_sub_comm]
      _ ≤ E/|J| := div_le_div_of_nonneg_right h (le_of_lt (abs_pos.mpr hJ))
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The nonnegative three-copy argument on an ARBITRARY old tree. Only the
geometric grouping of eligible paths is needed; all old paths and the test
are retained. This applies to the projected means of multi-leaf shapes. -/
theorem general_three_copy_bound_at (n d : ℕ) (hd : d < n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1)
    (S : PrescribedTree n) (a b : S.Leaf) (v : S.Internal)
    (hab : splitDepth S a b = d)
    (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (X : FinitePath Ω n → Fin N → ℝ)
    (hOld : ∀ c, splitDepth S a c = d → ∀ x : Sample Ω S,
      X (S.pathAt c x) = X (S.pathAt b x)) :
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt n T d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        (S.sampleLaw T).expect (fun x =>
          FiniteLaw.dot (X (S.pathAt a x)) (X (S.pathAt b x))^2) +
      pairObservableHistory T m S a d (fun x y => FiniteLaw.dot (X x) (X y))
        (fun x => FiniteLaw.dot (X (S.pathAt a x)) (X (S.pathAt b x))) := by
  classical
  let R := fun x y => FiniteLaw.dot (X x) (X y)
  let D := fun w : S.Internal => ((grow S w).sampleLaw T).expect (fun x =>
    (R (S.pathAt a (oldSample S w x)) (S.pathAt b (oldSample S w x)) -
      R ((grow S w).pathAt (oldLeaf S w a) x) ((grow S w).pathAt (newLeaf S w) x))^2)
  have hsum := pair_square_identity_general T m hend S a b d (by omega) hab R
    (fun c hc x => congrArg (FiniteLaw.dot (X (S.pathAt a x))) (hOld c hc x))
  have hnonneg (w : S.Internal) : 0 ≤ pairFreshCost S m a d w * D w :=
    mul_nonneg (pairFreshCost_nonneg S m hm hp a d w)
      (FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _))
  have hone : pairFreshCost S m a d v * D v ≤ ∑ w : S.Internal, pairFreshCost S m a d w * D w :=
    Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
  have hcost : pairFreshCost S m a d v = -gamma S m v := by
    unfold pairFreshCost
    rw [splitDepth_symm,splitDepth_new_old,hav,ite_eq_left rfl]
  have hD : D v = KernelTower.tripleExpectAt n T d
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) := by
    have q := triple_marginal (grow S v) T (oldLeaf S v a) (oldLeaf S v b) (newLeaf S v)
      d (by omega) (by simpa only [splitDepth_old_old] using hab)
      (by simpa only [splitDepth_symm (grow S v) (oldLeaf S v a),splitDepth_new_old] using hav)
      (by simpa only [splitDepth_symm (grow S v) (oldLeaf S v b),splitDepth_new_old] using hbv)
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2)
    simpa only [D,R,pathAt_oldLeaf,pathAt_newLeaf] using q
  rw [hcost,hD] at hone

  change (1/2:ℝ)*(∑ w : S.Internal, pairFreshCost S m a d w * D w) = _ at hsum
  unfold KernelTower.halfTripleDifferenceAt
  linarith


end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

noncomputable local instance matrixTripleDecidable_re2943d_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
omit [Fintype C] [DecidableEq C] in
/-- The old test may be the physical overlap, rather than the projected
one. Its replacement costs precisely its L2 projection error. -/
theorem pair_three_copy_test_bound (n d : ℕ) (hd : d < n) (K : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (x y : S.Leaf) (v : S.Internal)
    (hxy : splitDepth S x y = d) (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω n → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (f : Sample Ω S → ℝ) :
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
      pairObservableHistory K m S x d (fun z w => FiniteLaw.dot (X z) (X w)) f +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  let R := fun z w => FiniteLaw.dot (X z) (X w)
  let F := fun z : Sample Ω S => R (S.pathAt x z) (S.pathAt y z)
  have hR : ∀ z w, |R z w| ≤ 1 := fun z w => FiniteLaw.abs_dot_le_one _ _ (hX z) (hX w)
  have hδ : 0 ≤ m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ := sub_nonneg.mpr (hm (by simp))
  have hF : (S.sampleLaw K).expect (fun z => F z^2) ≤ 1 := by
    calc
      _ ≤ (S.sampleLaw K).expect (fun _ => 1) := FiniteLaw.expect_mono _ (fun z =>
        (sq_le_one_iff_abs_le_one _).mpr (hR _ _))
      _ = _ := FiniteLaw.expect_const _ _
  have henergy := general_three_copy_bound_at n d hd K m hm hp hend S x y v
    hxy hxv hyv X hOld
  have htest := pairObservableHistory_l2 K m S x d R (fun z => F z-f z) hR
  rw [pairObservableHistory_sub_test] at htest
  have htest' := (le_abs_self _).trans htest
  have hsq := mul_le_mul_of_nonneg_left hF hδ
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)*(S.sampleLaw K).expect (fun z => F z^2)+
      pairObservableHistory K m S x d R F at henergy
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+pairObservableHistory K m S x d R f+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z)
  linarith

/-- Pointwise-in-the-root crux of the shifted-shape induction. The first term
is SIGNED (not the expectation of its absolute value), so the physical
perturbation identity can be used after root averaging. Every error is an
actual single-copy L2 error and has the literal protected-history charge. -/
theorem matrix_three_copy_pointwise_sat_oai (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Bijective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
    (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
    (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω L → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
    let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-
      FiniteLaw.dot (X (T.pathAt (q a) z)) (X (T.pathAt (q c) z)))
    let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) + H/J + E*B/|J| +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  dsimp only
  let m := grid L 0 L
  let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
  let R := fun z w => FiniteLaw.dot (X z) (X w)
  let F := fun z : Sample Ω S => R (S.pathAt x z) (S.pathAt y z)
  let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
  let HP := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
  let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-R (T.pathAt (q a) z) (T.pathAt (q c) z))
  let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
  have hm := grid_strictMono hL
  have hp : ∀ j, 0 ≤ m j := grid_nonneg
  have hend : m (Fin.last L) = 1 := grid_last hL
  have hJ : J ≠ 0 := div_ne_zero (partialKappa_ne_zero T m hm hp _)
    (partialKappa_ne_zero T m hm hp _)
  have henergy := pair_three_copy_test_bound L d hd K m hm.monotone hp hend S x y v
    hxy hxv hyv X hX hOld f
  have hU : (Finset.univ.erase x).card ≤ leaves S := by
    exact (Finset.card_erase_le).trans (by simp only [Finset.card_univ, card_leaf]; rfl)
  have hproj : |H-HP| ≤ E*B := by
    simpa only [H, HP, E, B, m, weightedMatrixHistory] using
      (projection_history_difference hL Q T S q hq.2 hS K A
        (fun z => R (z a) (z c)) (c::cs) (Finset.univ.erase x) id (fun _ => x) f hf hU)
  have hpair : HP = J*pairObservableHistory K m S x d R f := by
    have h := matrixHistory_first_pair_sat T q hq.1 K m hm hp hend a c hac cs hcs hdis hfull S x R f
    simpa only [hqd] using h
  have happrox := signed_approximation hJ hproj
  rw [hpair,mul_div_cancel_left₀ _ hJ] at happrox
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+H/J+E*B/|J|+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z)
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+pairObservableHistory K m S x d R f+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z) at henergy
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise_sat_oai := @OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise_sat_oai
