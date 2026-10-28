-- Prove2me | solution 1 for OAI.DilutedSpinGlass.PrescribedTree.matrixHistory_first_pair_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:36:01.200837+00:00
-- url     : https://prove2.me/submissions/10714641-f0f9-4382-8daa-a141ad237724

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000

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

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_2
/-- Ancestry constraints with ALL existing references, not merely a local
subtree, are exactly the global eligible-old-leaf selector. -/
theorem referenceDivergence_oldAllowed {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R) (b : Leaf S) :
    (referenceDivergence S a d hd R).oldAllowed b ↔ matchesOldProfile S R a d b := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero =>
      change b.1 ∉ R.image (fun a => a.1) ↔
        ∀ r ∈ R, splitDepth (.node k C) b r = 0
      constructor
      · intro h r hr
        apply (splitDepth_node_zero C b r).mpr
        intro heq
        exact h (Finset.mem_image.mpr ⟨r,hr,heq.symm⟩)
      · intro h hb
        obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hb
        exact ((splitDepth_node_zero C b r).mp (h r hr)) heq.symm
    | succ d =>
      obtain ⟨i,a⟩ := a
      obtain ⟨j,b⟩ := b
      have hd' : d < n := by omega
      by_cases hji : j = i
      · subst j
        have hchild : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
        have hreduce : (referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).oldAllowed ⟨i,b⟩ ↔
            (referenceDivergence (C i) a d hd' (childRefs R i)).oldAllowed b := by
          change (∃ h : i = i,
            (referenceDivergence (C i) a d hd' (childRefs R i)).oldAllowed (h ▸ b)) ↔ _
          simp
        rw [hreduce, ih i a d hd' (childRefs R i) hchild b]
        constructor
        · intro h r hr
          obtain ⟨j,r⟩ := r
          by_cases hji : j = i
          · subst j
            have hh := h r ((mem_childRefs R i r).mpr hr)
            rw [splitDepth_same_child, splitDepth_same_child]
            omega
          · rw [splitDepth_diff_child C i j (Ne.symm hji),
              splitDepth_diff_child C i j (Ne.symm hji)]
            exact (Nat.min_zero _).symm
        · intro h r hr
          have hh := h ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
          rw [splitDepth_same_child, splitDepth_same_child] at hh
          omega
      · have hnone : ¬(referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).oldAllowed ⟨j,b⟩ := by
          change ¬∃ h : j = i, _
          exact fun ⟨h,_⟩ => hji h
        rw [iff_false_left hnone]
        intro h
        have hh := h ⟨i,a⟩ ha
        rw [splitDepth_diff_child C j i hji] at hh
        have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
          splitDepth_self _ _
        rw [hhself] at hh
        omega

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

/-- Fresh divergences satisfy exactly the same all-reference positional profile
as the old-choice selector; the profile is also the actual new leaf's profile
in the enlarged tree, by splitDepth_new_old. -/
theorem referenceDivergence_freshAllowed {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R) (v : Internal S) :
    (referenceDivergence S a d hd R).freshAllowed v ↔ matchesFreshProfile S R a d v := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases d with
    | zero =>
      cases v with
      | none =>
        change True ↔ ∀ r ∈ R, (0 : ℕ) = 0
        simp
      | some v =>
        obtain ⟨i,v⟩ := v
        change i ∉ R.image (fun a => a.1) ↔
          ∀ r ∈ R, freshSplitDepth (.node k C) (some ⟨i,v⟩) r = 0
        constructor
        · intro h r hr
          apply (freshSplitDepth_node_zero C i v r).mpr
          intro heq
          exact h (Finset.mem_image.mpr ⟨r,hr,heq⟩)
        · intro h hb
          obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hb
          exact ((freshSplitDepth_node_zero C i v r).mp (h r hr)) heq
    | succ d =>
      obtain ⟨i,a⟩ := a
      have hd' : d < n := by omega
      cases v with
      | none =>
        change False ↔ _
        rw [false_iff]
        intro h
        have hh := h ⟨i,a⟩ ha
        change 0 = min (d+1) (splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩) at hh
        have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
          splitDepth_self _ _
        rw [hhself] at hh
        omega
      | some v =>
        obtain ⟨j,v⟩ := v
        by_cases hji : j = i
        · subst j
          have hchild : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
          have hreduce : (referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).freshAllowed (some ⟨i,v⟩) ↔
              (referenceDivergence (C i) a d hd' (childRefs R i)).freshAllowed v := by
            change (∃ h : i = i,
              (referenceDivergence (C i) a d hd' (childRefs R i)).freshAllowed (h ▸ v)) ↔ _
            simp
          rw [hreduce, ih i a d hd' (childRefs R i) hchild v]
          constructor
          · intro h r hr
            obtain ⟨j,r⟩ := r
            by_cases hji : j = i
            · subst j
              have hh := h r ((mem_childRefs R i r).mpr hr)
              rw [freshSplitDepth_same_child, splitDepth_same_child]
              omega
            · rw [freshSplitDepth_diff_child C i j hji,
                splitDepth_diff_child C i j (Ne.symm hji)]
              exact (Nat.min_zero _).symm
          · intro h r hr
            have hh := h ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
            rw [freshSplitDepth_same_child, splitDepth_same_child] at hh
            omega
        · have hnone : ¬(referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).freshAllowed (some ⟨j,v⟩) := by
            change ¬∃ h : j = i, _
            exact fun ⟨h,_⟩ => hji h
          rw [iff_false_left hnone]
          intro h
          have hh := h ⟨i,a⟩ ha
          rw [freshSplitDepth_diff_child C j i (Ne.symm hji)] at hh
          have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
            splitDepth_self _ _
          rw [hhself] at hh
          omega

/-- The reference-path normalizing identity over globally admissible old or
fresh labels. No conditioning on sampled spin values occurs in the selector. -/
theorem reference_profile_total {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ b : Leaf S, if matchesOldProfile S R a d b then (1 : ℝ) else 0) +
      (∑ v : Internal S, if matchesFreshProfile S R a d v then gamma S m v else 0) =
      (referenceDivergence S a d hd R).coefficient m := by
  simp_rw [← referenceDivergence_oldAllowed S a d hd R ha,
    ← referenceDivergence_freshAllowed S a d hd R ha]
  exact divergence_choice_total _ m hend

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

noncomputable local instance instDecidable_4_r33eb5d_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Freshness is positional and survives deterministic or atomic spin laws. -/
theorem freshSplitDepth_lt {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    freshSplitDepth S v a < n := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact Nat.zero_lt_succ n
    | some v =>
      obtain ⟨i,v⟩ := v
      obtain ⟨j,a⟩ := a
      by_cases hji : j = i
      · subst j
        rw [freshSplitDepth_same_child]
        have := ih i v a
        omega
      · rw [freshSplitDepth_diff_child C i j hji]
        omega

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

theorem oldLeaf_injective {n : ℕ} (S : PrescribedTree n) (v : Internal S) :
    Function.Injective (oldLeaf S v) := by
  intro a b hab
  apply (splitDepth_eq_height S a b).mp
  rw [← splitDepth_old_old S v a b, hab, splitDepth_self]

theorem newLeaf_ne_oldLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    newLeaf S v ≠ oldLeaf S v a := by
  intro h
  have he := splitDepth_new_old S v a
  rw [h, splitDepth_self] at he
  have := freshSplitDepth_lt S v a
  omega

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_5
/-- A finite number of represented equivalence classes depends only on the
kernel relation, not on their ambient set of representatives. -/
theorem card_image_of_same_kernel {ι α β : Type*} [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (R : Finset ι) (f : ι → α) (g : ι → β)
    (h : ∀ i ∈ R, ∀ j ∈ R, f i = f j ↔ g i = g j) :
    (R.image f).card = (R.image g).card := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert a R ha ih =>
    have hR : ∀ i ∈ R, ∀ j ∈ R, f i = f j ↔ g i = g j := by
      intro i hi j hj
      exact h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have he : f a ∈ R.image f ↔ g a ∈ R.image g := by
      constructor
      · intro hh
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hh
        exact Finset.mem_image.mpr ⟨i,hi,(h i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self ..)).mp heq⟩
      · intro hg
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hg
        exact Finset.mem_image.mpr ⟨i,hi,(h i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self ..)).mpr heq⟩
    rw [Finset.image_insert, Finset.image_insert]
    by_cases hf : f a ∈ R.image f
    · rw [Finset.card_insert_of_mem hf, Finset.card_insert_of_mem (he.mp hf), ih hR]
    · rw [Finset.card_insert_of_notMem hf,
        Finset.card_insert_of_notMem (fun hg => hf (he.mpr hg)), ih hR]

theorem sigma_cast_snd {α : Type*} {β : α → Type*} (x : Sigma β) (i : α)
    (h : x.1 = i) : (⟨i,h ▸ x.2⟩ : Sigma β) = x := by
  obtain ⟨j,x⟩ := x
  dsimp at h
  subst i
  rfl

/-- Returning a restricted reference label to its original tree. -/
theorem childLabelLeaf_embed {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} (r : ι → Leaf (.node k C)) (i : Fin k) (l : ChildLabels r i) :
    (⟨i,childLabelLeaf r i l⟩ : Leaf (.node k C)) = r l.val := by
  exact sigma_cast_snd (r l.val) i l.property

/-- The child reference set really is the image of the child-restricted labels. -/
theorem childRefs_image {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} [Fintype ι] (r : ι → Leaf (.node k C)) (i : Fin k) :
    childRefs (Finset.univ.image r) i =
      Finset.univ.image (childLabelLeaf r i) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨l,_,hl⟩ := (Finset.mem_image (f := r)).mp ((mem_childRefs _ i b).mp hb)
    have hi : (r l).1 = i := congrArg Sigma.fst hl
    apply Finset.mem_image.mpr
    refine ⟨⟨l,hi⟩,Finset.mem_univ _, ?_⟩
    have he := (childLabelLeaf_embed r i ⟨l,hi⟩).trans hl
    exact eq_of_heq ((Sigma.mk.inj_iff.mp he).2)
  · intro hb
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hb
    apply (mem_childRefs _ i b).mpr
    exact (Finset.mem_image (f := r)).mpr ⟨l.val,Finset.mem_univ _, by
      rw [← childLabelLeaf_embed r i l, hl]⟩


/-- One-step signed reference normalization is determined by the entire
labeled splitting matrix, not by the unused old leaves of its realization. -/
theorem reference_coefficient_invariant {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    (referenceDivergence S (r a) d hd (Finset.univ.image r)).coefficient m =
      (referenceDivergence T (s a) d hd (Finset.univ.image s)).coefficient m := by
  classical
  induction n generalizing ι d with
  | zero => omega
  | succ n ih =>
    cases S with | node k C =>
    cases T with | node k' C' =>
    have hf (i j : ι) : (r i).1 = (r j).1 ↔ (s i).1 = (s j).1 := by
      have he := hsplit i j
      have hr := splitDepth_node_zero C (r i) (r j)
      have hs := splitDepth_node_zero C' (s i) (s j)
      rw [he] at hr
      tauto
    cases d with
    | zero =>
      change m 0 - (((Finset.univ.image r).image (fun b => b.1)).card : ℝ)*m 1 =
        m 0 - (((Finset.univ.image s).image (fun b => b.1)).card : ℝ)*m 1
      rw [Finset.image_image, Finset.image_image]
      have he := card_image_of_same_kernel Finset.univ (fun i => (r i).1)
        (fun i => (s i).1) (fun i _ j _ => hf i j)
      dsimp only [Function.comp_def]
      erw [he]
    | succ d =>
      let I := ChildLabels r (r a).1
      let rr : I → Leaf (C (r a).1) := childLabelLeaf r (r a).1
      let ss : I → Leaf (C' (s a).1) := fun l =>
        childLabelLeaf s (s a).1 ⟨l.val,(hf l.val a).mp l.property⟩
      let aa : I := ⟨a,rfl⟩
      have hr (i : I) : (⟨(r a).1,rr i⟩ : Leaf (.node k C)) = r i.val :=
        childLabelLeaf_embed r _ i
      have hs (i : I) : (⟨(s a).1,ss i⟩ : Leaf (.node k' C')) = s i.val :=
        childLabelLeaf_embed s _ _
      have hsplit' (i j : I) : splitDepth (C (r a).1) (rr i) (rr j) =
          splitDepth (C' (s a).1) (ss i) (ss j) := by
        have he := hsplit i.val j.val
        rw [← hr i, ← hr j, ← hs i, ← hs j,
          splitDepth_same_child, splitDepth_same_child] at he
        omega
      have hR := childRefs_image r (r a).1
      have hS : childRefs (Finset.univ.image s) (s a).1 = Finset.univ.image ss := by
        ext b
        constructor
        · intro hb
          obtain ⟨l,_,hl⟩ := (Finset.mem_image (f := s)).mp ((mem_childRefs _ _ b).mp hb)
          have hls : (s l).1 = (s a).1 := by
            have hh := congrArg (fun x : Leaf (.node k' C') => x.1) hl
            exact hh
          let l' : I := ⟨l,(hf l a).mpr hls⟩
          refine Finset.mem_image.mpr ⟨l',Finset.mem_univ _, ?_⟩
          have hh := (hs l').trans hl
          exact eq_of_heq ((Sigma.mk.inj_iff.mp hh).2)
        · intro hb
          obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hb
          apply (mem_childRefs _ _ b).mpr
          exact (Finset.mem_image (f := s)).mpr ⟨l.val,Finset.mem_univ _, by rw [← hs l, hl]⟩
      have hd' : d < n := by omega
      change (referenceDivergence (C (r a).1) (r a).2 d hd'
        (childRefs (Finset.univ.image r) (r a).1)).coefficient (fun j => m j.succ) =
        (referenceDivergence (C' (s a).1) (s a).2 d hd'
        (childRefs (Finset.univ.image s) (s a).1)).coefficient (fun j => m j.succ)
      rw [hR,hS]
      exact ih _ _ rr ss aa hsplit' d hd' _

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

noncomputable local instance instDecidable_6_r33eb5d_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Positional ancestry is an ultrametric similarity, independently of spins. -/
theorem splitDepth_ultrametric {n : ℕ} (S : PrescribedTree n) (a b c : Leaf S) :
    min (splitDepth S a b) (splitDepth S b c) ≤ splitDepth S a c := by
  induction S with
  | leaf => exact le_refl _
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    obtain ⟨l,c⟩ := c
    by_cases hij : i = j
    · subst j
      by_cases hil : i = l
      · subst l
        rw [splitDepth_same_child, splitDepth_same_child, splitDepth_same_child]
        have h := ih i a b c
        omega
      · rw [splitDepth_diff_child C i l hil, Nat.min_zero]
        exact Nat.zero_le _
    · rw [splitDepth_diff_child C i j hij, Nat.zero_min]
      exact Nat.zero_le _

 
theorem deepest_reference_profile {n : ℕ} (S : PrescribedTree n) (b a r : Leaf S)
    (hmax : splitDepth S b r ≤ splitDepth S b a) :
    splitDepth S b r = min (splitDepth S b a) (splitDepth S a r) := by
  have h1 := splitDepth_ultrametric S b a r
  have h2 := splitDepth_ultrametric S a b r
  rw [splitDepth_symm S a b, min_eq_right hmax] at h2
  exact le_antisymm (le_min hmax h2) h1

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_7
theorem labeledOldMatch_profile {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a)) (x : Leaf S) :
    labeledOldMatch S T r s b x ↔
      matchesOldProfile S (Finset.univ.image r) (r a) (splitDepth T b (s a)) x := by
  constructor
  · intro h y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    rw [h i, hsplit, deepest_reference_profile T b (s a) (s i) (hmax i)]
  · intro h i
    have hh := h (r i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hsplit] at hh
    rw [hh, deepest_reference_profile T b (s a) (s i) (hmax i)]

theorem labeledFreshMatch_profile {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a)) (v : Internal S) :
    labeledFreshMatch S T r s b v ↔
      matchesFreshProfile S (Finset.univ.image r) (r a) (splitDepth T b (s a)) v := by
  constructor
  · intro h y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    rw [h i, hsplit, deepest_reference_profile T b (s a) (s i) (hmax i)]
  · intro h i
    have hh := h (r i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hsplit] at hh
    rw [hh, deepest_reference_profile T b (s a) (s i) (hmax i)]

/-- Every eligible old or fresh choice is counted once. Its signed total
depends only on the prescribed reference splitting matrix. -/
theorem labeled_choice_total {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hne : b ≠ s a) (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a))
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ x : Leaf S, if labeledOldMatch S T r s b x then (1:ℝ) else 0) +
      (∑ v : Internal S, if labeledFreshMatch S T r s b v then gamma S m v else 0) =
      (referenceDivergence T (s a) (splitDepth T b (s a))
        (splitDepth_lt_of_ne T b (s a) hne) (Finset.univ.image s)).coefficient m := by
  simp_rw [labeledOldMatch_profile S T r s b a hsplit hmax,
    labeledFreshMatch_profile S T r s b a hsplit hmax]
  rw [reference_profile_total S (r a) (splitDepth T b (s a))
    (splitDepth_lt_of_ne T b (s a) hne) (Finset.univ.image r)
    (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) m hend]
  exact reference_coefficient_invariant S T r s a hsplit _ _ m

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

attribute [local instance 2000] OAI.DilutedSpinGlass.PrescribedTree.instDecidableEqLeaf_1
noncomputable local instance (priority := 2000) instDecidableEqSigma_r33eb5d_1 {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _
theorem branchProduct_succ (x y : ℝ) {k : ℕ} (hk : 0 < k) :
    branchProduct x y (k+1) = branchProduct x y k * (x-(k:ℝ)*y) := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  simp [branchProduct, Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]


theorem childRefs_insert_other {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i j : Fin k) (hij : j ≠ i) (a : Leaf (C i)) :
    childRefs (insert (⟨i,a⟩ : Leaf (.node k C)) R) j = childRefs R j := by
  classical
  ext b
  constructor
  · intro h
    have hh := (mem_childRefs _ j b).mp h
    rcases Finset.mem_insert.mp hh with hab | hb
    · exact (hij (congrArg Sigma.fst hab)).elim
    · exact (mem_childRefs R j b).mpr hb
  · intro h
    apply (mem_childRefs _ j b).mpr
    exact Finset.mem_insert_of_mem ((mem_childRefs R j b).mp h)

theorem childRefs_singleton_other {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (i j : Fin k) (hij : j ≠ i) (a : Leaf (C i)) :
    childRefs (C := C) ({⟨i,a⟩} : Finset (Leaf (.node k C))) j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hh := Finset.mem_singleton.mp ((mem_childRefs _ j b).mp hb)
  exact hij (congrArg Sigma.fst hh)

@[simp] theorem partialKappa_singleton {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (a : Leaf S) : partialKappa S m {a} = 1 := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    change branchProduct (m 0) (m 1) (Finset.image (fun a : Sigma (fun j => Leaf (C j)) => a.1) {⟨i,a⟩}).card * _ = 1
    rw [Finset.image_singleton,Finset.card_singleton,branchProduct_one,one_mul]
    apply Finset.prod_eq_one
    intro j _
    by_cases hji : j = i
    · subst j
      rw [childRefs_singleton_same]
      exact ih i (fun j => m j.succ) a
    · rw [childRefs_singleton_other i j hji,partialKappa_empty]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance 2000] OAI.DilutedSpinGlass.PrescribedTree.instDecidableEqLeaf_2
noncomputable local instance (priority := 2000) instDecidableEqSigma_1_r33eb5d_1 {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _
private theorem prod_local_factor {α : Type*} [Fintype α] (f g : α → ℝ) (i : α) (c : ℝ)
    (hi : f i = c*g i) (ho : ∀ j, j ≠ i → f j = g j) :
    (∏ j, f j) = c*∏ j, g j := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),hi]
  have he : (∏ j ∈ Finset.univ.erase i, f j) = ∏ j ∈ Finset.univ.erase i, g j :=
    Finset.prod_congr rfl (fun j hj => ho j (Finset.mem_erase.mp hj).1)
  rw [he,mul_assoc]

private theorem childRefs_eq_empty_of_unoccupied {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) (hi : i ∉ R.image (fun a => a.1)) :
    childRefs R i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact hi (Finset.mem_image.mpr ⟨⟨i,a⟩,(mem_childRefs R i a).mp ha,rfl⟩)

 
theorem partialKappa_insert {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (R : Finset (Leaf S)) (a b : Leaf S)
    (ha : a ∈ R) (hb : b ∉ R)
    (hmax : ∀ r ∈ R, splitDepth S b r ≤ splitDepth S b a) :
    partialKappa S m (insert b R) =
      (referenceDivergence S a (splitDepth S b a)
        (splitDepth_lt_of_ne S b a (fun h => hb (h ▸ ha))) R).coefficient m *
        partialKappa S m R := by
  classical
  induction S with
  | leaf =>
    have he : a = b := @Subsingleton.elim Unit (inferInstanceAs (Subsingleton Unit)) a b
    exact (hb (he ▸ ha)).elim
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases hji : j = i
    · subst j
      have hai : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
      have hbi : b ∉ childRefs R i := fun h => hb ((mem_childRefs R i b).mp h)
      have hmi : ∀ r ∈ childRefs R i, splitDepth (C i) b r ≤ splitDepth (C i) b a := by
        intro r hr
        have hh := hmax ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
        rw [splitDepth_same_child,splitDepth_same_child] at hh
        omega
      have hei : i ∈ R.image (fun r => r.1) := Finset.mem_image.mpr ⟨⟨i,a⟩,ha,rfl⟩
      have hroot : (insert (⟨i,b⟩ : Leaf (.node k C)) R).image (fun r => r.1) =
          R.image (fun r => r.1) := by
        erw [Finset.image_insert]
        exact Finset.insert_eq_of_mem hei
      let c := (referenceDivergence (C i) a (splitDepth (C i) b a)
        (splitDepth_lt_of_ne _ b a (fun h => hbi (h ▸ hai))) (childRefs R i)).coefficient
          (fun z => m z.succ)
      have hprod : (∏ t, partialKappa (C t) (fun z => m z.succ)
          (childRefs (insert (⟨i,b⟩ : Leaf (.node k C)) R) t)) =
          c*∏ t, partialKappa (C t) (fun z => m z.succ) (childRefs R t) := by
        apply prod_local_factor _ _ i c
        · rw [childRefs_insert_same]
          exact ih i (fun z => m z.succ) (childRefs R i) a b hai hbi hmi
        · intro t hti
          rw [childRefs_insert_other R i t hti]
      change branchProduct (m 0) (m 1) ((insert (⟨i,b⟩ : Leaf (.node k C)) R).image
        (fun r => r.1)).card * _ = _
      erw [hroot,hprod]
      simp only [splitDepth_same_child,Nat.add_comm 1]
      change branchProduct (m 0) (m 1) (R.image (fun r => r.1)).card * (c*_) =
        c*(branchProduct (m 0) (m 1) (R.image (fun r => r.1)).card * _)
      ring
    · have hz : splitDepth (.node k C) (⟨j,b⟩ : Leaf (.node k C)) ⟨i,a⟩ = 0 :=
        splitDepth_diff_child C j i hji b a
      have hj : j ∉ R.image (fun r => r.1) := by
        intro h
        obtain ⟨⟨t,r⟩,hr,ht⟩ := Finset.mem_image.mp h
        change t = j at ht
        subst t
        have hh := hmax ⟨j,r⟩ hr
        rw [hz,splitDepth_same_child] at hh
        omega
      have hchild := childRefs_eq_empty_of_unoccupied R j hj
      have hcard : 0 < (R.image (fun r => r.1)).card :=
        Finset.card_pos.mpr ⟨i,Finset.mem_image.mpr ⟨⟨i,a⟩,ha,rfl⟩⟩
      have hroot : ((insert (⟨j,b⟩ : Leaf (.node k C)) R).image (fun r => r.1)).card =
          (R.image (fun r => r.1)).card+1 := by
        erw [Finset.image_insert,Finset.card_insert_of_notMem hj]
      have hprod : (∏ t, partialKappa (C t) (fun z => m z.succ)
          (childRefs (insert (⟨j,b⟩ : Leaf (.node k C)) R) t)) =
          ∏ t, partialKappa (C t) (fun z => m z.succ) (childRefs R t) := by
        apply Finset.prod_congr rfl
        intro t _
        by_cases ht : t = j
        · subst t
          rw [childRefs_insert_same,hchild,Finset.insert_empty,partialKappa_singleton,
            partialKappa_empty]
        · rw [childRefs_insert_other R j t ht]
      change branchProduct (m 0) (m 1) ((insert (⟨j,b⟩ : Leaf (.node k C)) R).image
        (fun r => r.1)).card * _ = _
      erw [hroot,hprod,branchProduct_succ _ _ hcard]
      simp only [hz]
      change (_ * (m 0-((R.image (fun r => r.1)).card : ℝ)*m 1))*_ =
        (m 0-((R.image (fun r => r.1)).card : ℝ)*m 1)*(_*_)
      ring

end DilutedSpinGlass.PrescribedTree

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

noncomputable local instance treeMarkLawPropDecidable_r33eb5d_1 (proposition : Prop) :
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_HistoryDistinct
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
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

lemma HistoryValid.pick_old {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryValid S U loc P pos)
    {c : C} (hc : c ∉ P) {i : ι} (hi : i ∈ U) :
    HistoryValid S (U.erase i) loc (insert c P) (Function.update pos c (loc i)) := by
  refine ⟨h.loc_inj,?_,?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; rfl
    · subst a
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_self,Function.update_of_ne hbc] at hab
      exact False.elim (h.disjoint i hi b hb hab)
    · subst b
      have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_self,Function.update_of_ne hac] at hab
      exact False.elim (h.disjoint i hi a ha hab.symm)
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_of_ne hac,Function.update_of_ne hbc] at hab
      exact h.pos_inj ha hb hab
  · intro j hj a ha
    rcases Finset.mem_erase.mp hj with ⟨hji,hj⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa only [Function.update_self] using (fun e => hji (h.loc_inj e))
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      simpa only [Function.update_of_ne hac] using h.disjoint j hj a ha

omit [DecidableEq ι] in
lemma HistoryValid.pick_fresh {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryValid S U loc P pos)
    {c : C} (hc : c ∉ P) (v : S.Internal) :
    HistoryValid (grow S v) U (fun i => oldLeaf S v (loc i)) (insert c P)
      (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v)) := by
  refine ⟨(oldLeaf_injective S v).comp h.loc_inj,?_,?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; rfl
    · subst a
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_self,Function.update_of_ne hbc] at hab
      exact False.elim (newLeaf_ne_oldLeaf S v (pos b) hab)
    · subst b
      have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_self,Function.update_of_ne hac] at hab
      exact False.elim (newLeaf_ne_oldLeaf S v (pos a) hab.symm)
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_of_ne hac,Function.update_of_ne hbc] at hab
      exact h.pos_inj ha hb (oldLeaf_injective S v hab)
  · intro i hi a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa only [Function.update_self] using (newLeaf_ne_oldLeaf S v (loc i)).symm
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_of_ne hac]
      exact fun e => h.disjoint i hi a ha (oldLeaf_injective S v e)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProfileHistory
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
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

/-- Growth adds exactly one new positional leaf, not just one spin value. -/
theorem grow_leaf_cases (S : PrescribedTree n) (v : S.Internal) (b : (grow S v).Leaf) :
    b = newLeaf S v ∨ ∃ a, b = oldLeaf S v a := by
  classical
  let F : Option S.Leaf → (grow S v).Leaf := Option.elim' (newLeaf S v) (oldLeaf S v)
  have hinj : Function.Injective F := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (newLeaf_ne_oldLeaf S v _ h)
    · exact False.elim (newLeaf_ne_oldLeaf S v _ h.symm)
    · exact congrArg some (oldLeaf_injective S v h)
  have hcard : Fintype.card (Option S.Leaf) = Fintype.card (grow S v).Leaf := by
    simp only [Fintype.card_option,card_leaf,leaves_grow]
  have hs := ((Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj,hcard⟩).2
  obtain ⟨a,rfl⟩ := hs b
  cases a with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a,rfl⟩

lemma HistoryCover.pick_old {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryCover S U loc P pos)
    {c : C} (hc : c ∉ P) {i : ι} (hi : i ∈ U) :
    HistoryCover S (U.erase i) loc (insert c P) (Function.update pos c (loc i)) := by
  refine ⟨h.toHistoryValid.pick_old hc hi,?_⟩
  intro b
  rcases h.cover b with ⟨j,hj,rfl⟩ | ⟨d,hd,rfl⟩
  · by_cases hji : j = i
    · subst j
      exact Or.inr ⟨c,Finset.mem_insert_self _ _,by simp only [Function.update_self]⟩
    · exact Or.inl ⟨j,Finset.mem_erase.mpr ⟨hji,hj⟩,rfl⟩
  · refine Or.inr ⟨d,Finset.mem_insert_of_mem hd,?_⟩
    simp only [Function.update_of_ne (fun he : d = c => hc (he ▸ hd))]

omit [DecidableEq ι] in
lemma HistoryCover.pick_fresh {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryCover S U loc P pos)
    {c : C} (hc : c ∉ P) (v : S.Internal) :
    HistoryCover (grow S v) U (fun i => oldLeaf S v (loc i)) (insert c P)
      (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v)) := by
  refine ⟨h.toHistoryValid.pick_fresh hc v,?_⟩
  intro b
  rcases grow_leaf_cases S v b with rfl | ⟨a,rfl⟩
  · exact Or.inr ⟨c,Finset.mem_insert_self _ _,by simp only [Function.update_self]⟩
  · rcases h.cover a with ⟨i,hi,rfl⟩ | ⟨d,hd,rfl⟩
    · exact Or.inl ⟨i,hi,rfl⟩
    · refine Or.inr ⟨d,Finset.mem_insert_of_mem hd,?_⟩
      simp only [Function.update_of_ne (fun he : d = c => hc (he ▸ hd))]

omit [DecidableEq C] [DecidableEq ι] in
/-- Available-old sums equal unrestricted old-leaf sums for any observable
that vanishes on the protected references. No probability calculation occurs. -/
lemma HistoryCover.sum_available {S : PrescribedTree n} {U : Finset ι}
    {loc : ι → S.Leaf} {P : Finset C} {pos : C → S.Leaf}
    (h : HistoryCover S U loc P pos) (F : S.Leaf → ℝ)
    (hF : ∀ c ∈ P, F (pos c) = 0) :
    (∑ i ∈ U, F (loc i)) = ∑ b : S.Leaf, F b := by
  classical
  rw [← Finset.sum_image (fun i _ j _ hij => h.loc_inj hij)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  rcases h.cover b with ⟨i,hi,rfl⟩ | ⟨c,hc,rfl⟩
  · exact False.elim (hb (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
  · exact hF c hc

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
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixHistoryDecidable_r33eb5d_1 (p : Prop) : Decidable p :=
  Classical.propDecidable p
/-- Once two assigned colors have the wrong split, no future legal extension
can repair it. This justifies enforcing the matrix constraints successively. -/
lemma matrixHistory_mismatch (T : PrescribedTree n) (q : C → T.Leaf)
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (a b : C) (ha : a ∉ cs) (hb : b ∉ cs)
    (he : splitDepth S (pos a) (pos b) ≠ splitDepth T (q a) (q b)) :
    matrixHistory T q K m cs S U loc pos f = 0 := by
  induction cs generalizing S U with
  | nil =>
    exact ite_eq_right (fun h => he (h a b))
  | cons c cs ih =>
    have hac : a ≠ c := fun h => ha (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have ha' : a ∉ cs := fun h => ha (by simp [h])
    have hb' : b ∉ cs := fun h => hb (by simp [h])
    change (∑ i ∈ U, matrixHistory T q K m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) +
      ∑ v : S.Internal, gamma S m v * matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0
    have ho (i : ι) : matrixHistory T q K m cs S (U.erase i) loc
        (Function.update pos c (loc i)) f = 0 := by
      apply ih S (U.erase i) loc _ f ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc] using he
    have hfresh (v : S.Internal) : matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0 := by
      apply ih (grow S v) U _ _ _ ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc,splitDepth_old_old] using he
    simp only [ho,hfresh,mul_zero,Finset.sum_const_zero,add_zero]

/-- Exact sequential enforcement of the full split matrix inside the
protected signed history. Impossible branches vanish, rather than being
silently dropped or replaced by a reference law. -/
theorem matrixHistory_step (T : PrescribedTree n) (q : C → T.Leaf)
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ) (c : C) (cs : List C)
    (P : Finset C) (hc : c ∉ P) (hdis : ∀ d ∈ cs, d ∉ insert c P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    matrixHistory T q K m (c::cs) S U loc pos f =
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) +
    ∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v * matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) else 0 := by
  have hc' : c ∉ cs := fun h => hdis c h (Finset.mem_insert_self _ _)
  have hd' : ∀ d ∈ P, d ∉ cs := fun d hd h => hdis d h (Finset.mem_insert_of_mem hd)
  change (_ + _) = _
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      apply matrixHistory_mismatch T q K m cs S (U.erase i) loc _ f c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd))] using he
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      suffices hh : matrixHistory T q K m cs (grow S v) U
          (fun i => oldLeaf S v (loc i))
          (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
          (fun x => f (oldSample S v x)) = 0 by
        simpa only [matrixHistory,mul_zero] using congrArg (gamma S m v * ·) hh
      apply matrixHistory_mismatch T q K m cs (grow S v) U _ _ _ c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd)),
        splitDepth_new_old] using he

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance kappaRegularDecidable_r33eb5d_1 (p : Prop) : Decidable p :=
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

variable {n : ℕ} {C ι : Type} [Fintype C] [DecidableEq C] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual one-step protected extension total is the ratio of the two
unordered branching products. Complete split constraints, not a surrogate
probability mechanism, determine this coefficient. -/
theorem matrix_choice_kappa (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (P : Finset C) (hP : P.Nonempty)
    (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (U : Finset ι) (loc : ι → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1) :
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then (1:ℝ) else 0) +
    (∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v else 0) =
    partialKappa T m ((insert c P).image q) / partialKappa T m (P.image q) := by
  classical
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image P (fun a => splitDepth T (q c) (q a)) hP
  let r : P → S.Leaf := fun a => pos a
  let s : P → T.Leaf := fun a => q a
  have himage : Finset.univ.image s = P.image q := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨b,b.property,hb⟩
    · rintro ⟨b,hb,he⟩
      exact ⟨⟨b,hb⟩,he⟩
  have hqa : q c ≠ q a := fun h => hc (hq h ▸ ha)
  have hn : q c ∉ P.image q := by
    rintro h
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp h
    exact hc (hq he ▸ hd)
  have he := labeled_choice_total S T r s (q c) ⟨a,ha⟩
    (fun a b => hsplit a a.property b b.property) hqa (fun b => hmax b b.property) m hend
  have ho (b : S.Leaf) : labeledOldMatch S T r s (q c) b ↔
      ∀ d ∈ P, splitDepth S b (pos d) = splitDepth T (q c) (q d) := by
    simp only [labeledOldMatch,r,s,Subtype.forall]
  have hf (v : S.Internal) : labeledFreshMatch S T r s (q c) v ↔
      ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d) := by
    simp only [labeledFreshMatch,r,s,Subtype.forall]
  simp_rw [ho,hf] at he
  have hav := hcover.sum_available
    (fun b => if ∀ d ∈ P, splitDepth S b (pos d) = splitDepth T (q c) (q d) then (1:ℝ) else 0)
    (by
      intro d hd
      apply ite_eq_right
      intro h
      have hh := h d hd
      rw [splitDepth_self] at hh
      exact hc (hq ((splitDepth_eq_height T (q c) (q d)).mp hh.symm) ▸ hd))
  rw [hav,he]
  have hk := partialKappa_insert T m (P.image q) (q a) (q c)
    (Finset.mem_image.mpr ⟨a,ha,rfl⟩) hn
    (by rintro t ht; obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ht; exact hmax d hd)
  rw [Finset.image_insert,hk]
  rw [mul_div_cancel_right₀ _ (partialKappa_ne_zero T m hm hp _)]
  simp only [himage,s]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixNormalization
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
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixNormalizationDecidable_r33eb5d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype C] in
lemma splitOn_pick_old (T S : PrescribedTree n) (q : C → T.Leaf)
    (P : Finset C) (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (x : S.Leaf)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (hx : ∀ a ∈ P, splitDepth S x (pos a) = splitDepth T (q c) (q a)) :
    ∀ a ∈ insert c P, ∀ b ∈ insert c P,
      splitDepth S (Function.update pos c x a) (Function.update pos c x b) =
        splitDepth T (q a) (q b) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with hac | ha <;> rcases Finset.mem_insert.mp hb with hbc | hb
  · subst a; subst b
    simp only [splitDepth_self]
  · subst a
    simpa only [Function.update_self,Function.update_of_ne (fun he : b = c => hc (he ▸ hb))] using hx b hb
  · subst b
    rw [splitDepth_symm,splitDepth_symm T (q a)]
    simpa only [Function.update_self,Function.update_of_ne (fun he : a = c => hc (he ▸ ha))] using hx a ha
  · simpa only [Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      Function.update_of_ne (fun he : b = c => hc (he ▸ hb))] using hsplit a ha b hb

omit [Fintype C] in
lemma splitOn_pick_fresh (T S : PrescribedTree n) (q : C → T.Leaf)
    (P : Finset C) (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (v : S.Internal)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (hv : ∀ a ∈ P, freshSplitDepth S v (pos a) = splitDepth T (q c) (q a)) :
    ∀ a ∈ insert c P, ∀ b ∈ insert c P,
      splitDepth (grow S v)
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) a)
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) b) =
        splitDepth T (q a) (q b) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with hac | ha <;> rcases Finset.mem_insert.mp hb with hbc | hb
  · subst a; subst b
    simp only [splitDepth_self]
  · subst a
    simpa only [Function.update_self,Function.update_of_ne (fun he : b = c => hc (he ▸ hb)),
      splitDepth_new_old] using hv b hb
  · subst b
    rw [splitDepth_symm,splitDepth_symm T (q a)]
    simpa only [Function.update_self,Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      splitDepth_new_old] using hv a ha
  · simpa only [Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      Function.update_of_ne (fun he : b = c => hc (he ▸ hb)),splitDepth_old_old] using hsplit a ha b hb

/-- Exact normalization of the ACTUAL complete-matrix protected history,
retaining an arbitrary old test. This bridges the analytic history to the
unordered kappa product, without assuming a reference-history identity. -/
theorem matrixHistory_normalization (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C) (hP : P.Nonempty)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (f : Sample Ω S → ℝ) :
    matrixHistory T q K m cs S U loc pos f =
      (partialKappa T m (Finset.univ.image q) / partialKappa T m (P.image q)) *
        (S.sampleLaw K).expect f := by
  classical
  induction cs generalizing P S U with
  | nil =>
    have he : P = Finset.univ := by simpa using hfull
    have hall : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b) := by
      intro a b
      apply hsplit a (by simp [he]) b (by simp [he])
    simp only [matrixHistory,labeledHistory,ite_eq_left hall,he,
      div_self (partialKappa_ne_zero T m hm hp _),one_mul]
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hcs' := (List.nodup_cons.mp hcs).2
    have hdis' : ∀ d ∈ cs, d ∉ insert c P := by
      intro d hd hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact (List.nodup_cons.mp hcs).1 hd
      · exact hdis d (by simp [hd]) hh
    have hfull' : insert c P ∪ cs.toFinset = Finset.univ := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hfull
    let A := partialKappa T m (Finset.univ.image q) / partialKappa T m ((insert c P).image q)
    have ho (i : ι) (hi : i ∈ U) :
        (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) =
        (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d) then (1:ℝ) else 0) *
          (A * (S.sampleLaw K).expect f) := by
      split_ifs with hx
      · rw [ih hcs' (insert c P) (Finset.insert_nonempty _ _) hdis' hfull' S (U.erase i) loc _
          (hcover.pick_old hc hi) (splitOn_pick_old T S q P c hc pos (loc i) hsplit hx) f]
        exact (one_mul _).symm
      · simp only [zero_mul]
    have hfresh (v : S.Internal) :
        (if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
          then gamma S m v * matrixHistory T q K m cs (grow S v) U
            (fun i => oldLeaf S v (loc i))
            (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
            (fun x => f (oldSample S v x)) else 0) =
        (if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
          then gamma S m v else 0) * (A * (S.sampleLaw K).expect f) := by
      split_ifs with hv
      · rw [ih hcs' (insert c P) (Finset.insert_nonempty _ _) hdis' hfull' (grow S v) U _ _
          (hcover.pick_fresh hc v) (splitOn_pick_fresh T S q P c hc pos v hsplit hv) _,grow_projectivity]
      · simp only [zero_mul]
    rw [matrixHistory_step T q K m c cs P hc hdis']
    have hh : (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) =
        ∑ i ∈ U, (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then (1:ℝ) else 0) * (A * (S.sampleLaw K).expect f) := Finset.sum_congr rfl ho
    rw [hh]
    simp_rw [hfresh]
    rw [← Finset.sum_mul,← Finset.sum_mul,← add_mul,
      matrix_choice_kappa T S q hq P hP c hc pos U loc hcover hsplit m hm hp hend]
    dsimp only [A]
    rw [← mul_assoc, div_mul_div_cancel₀'
      (partialKappa_ne_zero T m hm hp ((insert c P).image q))]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance weightedMatrixHistoryDecidable_r33eb5d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype Ω] in
/-- Once two assigned colors have the wrong split, no future legal extension
can repair it. This justifies enforcing the matrix constraints successively. -/
lemma weightedMatrixHistory_mismatch (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ) (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (a b : C) (ha : a ∉ cs) (hb : b ∉ cs)
    (he : splitDepth S (pos a) (pos b) ≠ splitDepth T (q a) (q b)) :
    weightedMatrixHistory T q V m cs S U loc pos f = 0 := by
  induction cs generalizing S U with
  | nil =>
    exact ite_eq_right (fun h => he (h a b))
  | cons c cs ih =>
    have hac : a ≠ c := fun h => ha (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have ha' : a ∉ cs := fun h => ha (by simp [h])
    have hb' : b ∉ cs := fun h => hb (by simp [h])
    change (∑ i ∈ U, weightedMatrixHistory T q V m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) +
      ∑ v : S.Internal, gamma S m v * weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0
    have ho (i : ι) : weightedMatrixHistory T q V m cs S (U.erase i) loc
        (Function.update pos c (loc i)) f = 0 := by
      apply ih S (U.erase i) loc _ f ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc] using he
    have hfresh (v : S.Internal) : weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0 := by
      apply ih (grow S v) U _ _ _ ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc,splitDepth_old_old] using he
    simp only [ho,hfresh,mul_zero,Finset.sum_const_zero,add_zero]

omit [Fintype Ω] in
/-- Exact sequential enforcement of the full split matrix inside the
protected signed history. Impossible branches vanish, rather than being
silently dropped or replaced by a reference law. -/
theorem weightedMatrixHistory_step (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ) (m : Fin (n+1) → ℝ) (c : C) (cs : List C)
    (P : Finset C) (hc : c ∉ P) (hdis : ∀ d ∈ cs, d ∉ insert c P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q V m (c::cs) S U loc pos f =
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then weightedMatrixHistory T q V m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) +
    ∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v * weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) else 0 := by
  have hc' : c ∉ cs := fun h => hdis c h (Finset.mem_insert_self _ _)
  have hd' : ∀ d ∈ P, d ∉ cs := fun d hd h => hdis d h (Finset.mem_insert_of_mem hd)
  change (_ + _) = _
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      apply weightedMatrixHistory_mismatch T q V m cs S (U.erase i) loc _ f c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd))] using he
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      suffices hh : weightedMatrixHistory T q V m cs (grow S v) U
          (fun i => oldLeaf S v (loc i))
          (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
          (fun x => f (oldSample S v x)) = 0 by
        simpa only [weightedMatrixHistory,mul_zero] using congrArg (gamma S m v * ·) hh
      apply weightedMatrixHistory_mismatch T q V m cs (grow S v) U _ _ _ c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd)),
        splitDepth_new_old] using he

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HistoryRetained
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
variable {Ω C ι : Type} [Fintype Ω] [DecidableEq C] [DecidableEq ι] {n : ℕ}

omit [Fintype Ω] in
/-- A function of protected paths is transported jointly with the full old
test through EVERY fresh extension. This is an identity of signed histories. -/
theorem labeledHistory_protected_function (m : Fin (n+1) → ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (P : Finset C) (G : (C → FinitePath Ω n) → ℝ)
    (hG : ∀ x y, (∀ c ∈ P, x c = y c) → G x = G y)
    (cs : List C) (hdis : ∀ c ∈ cs, c ∉ P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => V R pos (fun x => g x * G (fun c => R.pathAt (pos c) x)))
      cs S U loc pos f =
    labeledHistory m V cs S U loc pos (fun x => f x*G (fun c => S.pathAt (pos c) x)) := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hdis' : ∀ d ∈ cs, d ∉ P := fun d hd => hdis d (by simp [hd])
    simp only [labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ih hdis']
      congr 1
      funext x
      congr 1
      apply hG
      intro d hd
      rw [Function.update_of_ne (fun h : d = c => hc (h ▸ hd))]
    · apply Finset.sum_congr rfl
      intro v _
      congr 1
      rw [ih hdis']
      congr 1
      funext x
      congr 1
      apply hG
      intro d hd
      rw [Function.update_of_ne (fun h : d = c => hc (h ▸ hd)),pathAt_oldLeaf]

variable [Fintype C]

noncomputable local instance historyRetainedPropDecidable_r33eb5d_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- Complete-matrix normalization WITH any observable of the already assigned
paths. Its joint dependence on the old test and the original samples is kept. -/
theorem matrixHistory_retained (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C) (hP : P.Nonempty)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (G : (C → FinitePath Ω n) → ℝ)
    (hG : ∀ x y, (∀ c ∈ P, x c = y c) → G x = G y)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => if ∀ a b,
      splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
      then (R.sampleLaw K).expect (fun x => g x*G (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f =
    (partialKappa T m (Finset.univ.image q) / partialKappa T m (P.image q)) *
      (S.sampleLaw K).expect (fun x => f x*G (fun c => S.pathAt (pos c) x)) := by
  rw [labeledHistory_protected_function m
    (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
      then (R.sampleLaw K).expect g else 0) P G hG cs hdis]
  exact matrixHistory_normalization T q hq K m hm hp hend cs hcs P hP hdis hfull
    S U loc pos hcover hsplit _

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixPair
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
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {n : ℕ}

noncomputable local instance matrixPairPropDecidable_r33eb5d_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
omit [Fintype C] [DecidableEq C] in
lemma singleton_history_cover (S : PrescribedTree n) (x : S.Leaf) (a : C) :
    HistoryCover S (Finset.univ.erase x) id ({a} : Finset C) (fun _ => x) := by
  classical
  refine ⟨⟨Function.injective_id,?_,?_⟩,?_⟩
  · intro c hc d hd _
    simp only [Finset.mem_coe,Finset.mem_singleton] at hc hd
    exact hc.trans hd.symm
  · intro y hy c _
    exact (Finset.mem_erase.mp hy).1
  · intro y
    by_cases h : y = x
    · exact Or.inr ⟨a,by simp,h⟩
    · exact Or.inl ⟨y,by simp [h],rfl⟩

/-- The actual full prescribed split-matrix history, retaining just the anchor
and the first newly assigned path, is its exact kappa ratio times the literal
one-color pair history. All unused old replicas and their joint test remain.
This is not a reference-history assumption. -/
theorem matrixHistory_first_pair_sat_oai (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect
        (fun z => g z * R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f =
    (partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)) *
      pairObservableHistory K m S x (splitDepth T (q a) (q c)) R f := by
  classical
  let P : Finset C := {a}
  have hc : c ∉ P := by simpa only [P,Finset.mem_singleton] using hac.symm
  have hcover := singleton_history_cover S x a
  have hsplit : ∀ b ∈ P, ∀ d ∈ P,
      splitDepth S ((fun _ : C => x) b) ((fun _ : C => x) d) = splitDepth T (q b) (q d) := by
    intro b hb d hd
    have hb' : b = a := Finset.mem_singleton.mp hb
    have hd' : d = a := Finset.mem_singleton.mp hd
    subst b; subst d
    simp only [splitDepth_self]
  let G : (C → FinitePath Ω n) → ℝ := fun y => R (y a) (y c)
  have hG : ∀ y z, (∀ b ∈ insert c P, y b = z b) → G y = G z := by
    intro y z h
    dsimp only [G]
    rw [h a (by simp [P]),h c (by simp)]
  let A := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c P).image q)
  let V := fun (D : PrescribedTree n) (pos : C → D.Leaf) (g : Sample Ω D → ℝ) =>
    (D.sampleLaw K).expect (fun z => g z * R (D.pathAt (pos a) z) (D.pathAt (pos c) z))
  have old (y : S.Leaf) (hy : y ∈ Finset.univ.erase x)
      (hs : splitDepth S x y = splitDepth T (q a) (q c)) :
      weightedMatrixHistory T q V m cs S ((Finset.univ.erase x).erase y) id
        (Function.update (fun _ => x) c y) f =
      A * (S.sampleLaw K).expect (fun z => f z * R (S.pathAt x z) (S.pathAt y z)) := by
    have hs' : ∀ b ∈ P, splitDepth S (id y) ((fun _ : C => x) b) = splitDepth T (q c) (q b) := by
      intro b hb
      have hb' : b = a := Finset.mem_singleton.mp hb
      subst b
      simpa only [id_eq,splitDepth_symm S y x,splitDepth_symm T (q c) (q a)] using hs
    have h := matrixHistory_retained T q hq K m hm hp hend cs hcs (insert c P)
      (Finset.insert_nonempty _ _) hdis hfull G hG S ((Finset.univ.erase x).erase y) id _
      (hcover.pick_old hc hy) (splitOn_pick_old T S q P c hc _ y hsplit hs') f
    simpa only [weightedMatrixHistory,V,G,A,id_eq,Function.update_self,Function.update_of_ne hac] using h
  have fresh (v : S.Internal)
      (hs : splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c)) :
      weightedMatrixHistory T q V m cs (grow S v) (Finset.univ.erase x)
        (fun y => oldLeaf S v (id y))
        (Function.update (fun _ => oldLeaf S v x) c (newLeaf S v))
        (fun z => f (oldSample S v z)) =
      A * ((grow S v).sampleLaw K).expect (fun z => f (oldSample S v z) *
        R ((grow S v).pathAt (oldLeaf S v x) z) ((grow S v).pathAt (newLeaf S v) z)) := by
    have hs' : ∀ b ∈ P, freshSplitDepth S v ((fun _ : C => x) b) = splitDepth T (q c) (q b) := by
      intro b hb
      have hb' : b = a := Finset.mem_singleton.mp hb
      subst b
      simpa only [splitDepth_symm (grow S v) (oldLeaf S v x),splitDepth_new_old,
        splitDepth_symm T (q a) (q c)] using hs
    have h := matrixHistory_retained T q hq K m hm hp hend cs hcs (insert c P)
      (Finset.insert_nonempty _ _) hdis hfull G hG (grow S v) (Finset.univ.erase x) _ _
      (hcover.pick_fresh hc v) (splitOn_pick_fresh T S q P c hc _ v hsplit hs')
      (fun z => f (oldSample S v z))
    simpa only [weightedMatrixHistory,V,G,A,id_eq,Function.update_self,Function.update_of_ne hac] using h
  change weightedMatrixHistory T q V m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f = _
  rw [weightedMatrixHistory_step T q V m c cs P hc hdis]
  have ho (y : S.Leaf) (hy : y ∈ Finset.univ.erase x) :
      (if ∀ d ∈ P, splitDepth S (id y) ((fun _ : C => x) d) = splitDepth T (q c) (q d)
        then weightedMatrixHistory T q V m cs S ((Finset.univ.erase x).erase y) id
          (Function.update (fun _ => x) c (id y)) f else 0) =
      A * (if splitDepth S x y = splitDepth T (q a) (q c)
        then (S.sampleLaw K).expect (fun z => f z * R (S.pathAt x z) (S.pathAt y z)) else 0) := by
    have he : (∀ d ∈ P, splitDepth S (id y) ((fun _ : C => x) d) = splitDepth T (q c) (q d)) ↔
        splitDepth S x y = splitDepth T (q a) (q c) := by
      simp only [P,Finset.mem_singleton,forall_eq,id_eq,splitDepth_symm S y x,splitDepth_symm T (q c) (q a)]
    simp only [he]
    split_ifs with hs
    · exact old y hy hs
    · exact (mul_zero A).symm
  have hv (v : S.Internal) :
      (if ∀ d ∈ P, freshSplitDepth S v ((fun _ : C => x) d) = splitDepth T (q c) (q d)
        then gamma S m v * weightedMatrixHistory T q V m cs (grow S v) (Finset.univ.erase x)
          (fun y => oldLeaf S v (id y))
          (Function.update (fun _ => oldLeaf S v x) c (newLeaf S v))
          (fun z => f (oldSample S v z)) else 0) =
      A * (if splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c)
        then gamma S m v * ((grow S v).sampleLaw K).expect (fun z => f (oldSample S v z) *
          R ((grow S v).pathAt (oldLeaf S v x) z) ((grow S v).pathAt (newLeaf S v) z)) else 0) := by
    have he : (∀ d ∈ P, freshSplitDepth S v ((fun _ : C => x) d) = splitDepth T (q c) (q d)) ↔
        splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c) := by
      simp only [P,Finset.mem_singleton,forall_eq,splitDepth_symm (grow S v) (oldLeaf S v x),
        splitDepth_new_old,splitDepth_symm T (q a) (q c)]
    simp only [he]
    split_ifs with hs
    · rw [fresh v hs]; ring
    · exact (mul_zero A).symm
  have he := Finset.sum_congr rfl ho
  rw [he]
  simp_rw [hv]
  rw [← Finset.mul_sum,← Finset.mul_sum,← mul_add]
  rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.PrescribedTree.matrixHistory_first_pair_sat_oai := @OAI.DilutedSpinGlass.PrescribedTree.matrixHistory_first_pair_sat_oai
