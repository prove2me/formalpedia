-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl.singleton_regular_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:38:23.154653+00:00
-- url     : https://prove2.me/submissions/6dfc0e74-a6cd-4ab5-b995-294ff213b1a9

import Mathlib
import Definitions.Def_DilutedSpin
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

theorem covariance_centered (f g : Ω → ℝ) :
    P.covariance f g = P.expect (fun x => (f x - P.expect f) * (g x - P.expect g)) := by
  rw [covariance]
  calc
    _ = P.expect (fun x => f x * g x - f x * P.expect g -
        P.expect f * g x + P.expect f * P.expect g) := by simp
    _ = _ := P.expect_congr (fun x => by ring)

/-- Two independent centered copies have second moment twice the covariance. -/
theorem difference_product (f g : Ω → ℝ) :
    P.expect (fun y => P.expect (fun z => (f y - f z) * (g y - g z))) =
      2 * P.covariance f g := by
  calc
    _ = P.expect (fun y => P.expect (fun z =>
        f y * g y - f y * g z - f z * g y + f z * g z)) := by
          apply P.expect_congr
          intro y
          exact P.expect_congr (fun z => by ring)
    _ = _ := by simp [covariance]; ring

variable {n : ℕ}

theorem dot_sub_right (x y z : Fin n → ℝ) :
    dot x y - dot x z = dot x (fun i => y i - z i) := by
  simp [dot, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem dot_sq (x y : Fin n → ℝ) :
    dot x y ^ 2 = (∑ i, ∑ j, x i * x j * (y i * y j)) / (n : ℝ)^2 := by
  rw [dot, div_pow, pow_two, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact finite-conditional-law three-copy identity, with a square remainder.
No boundedness assumption is needed for this algebraic ingredient. -/
theorem three_copy_identity (X : Ω → Fin n → ℝ) :
    P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) =
    (2 / (n : ℝ)^2) *
      ((∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j)^2) +
        P.expect (fun x => (∑ i, P.expect (fun y => X y i) *
          (X x i - P.expect (fun y => X y i)))^2)) := by
  let μ : Fin n → ℝ := fun i => P.expect (fun x => X x i)
  let C : Fin n → Fin n → ℝ := fun i j =>
    P.covariance (fun x => X x i) (fun x => X x j)
  have hrem : P.expect (fun x => (∑ i, μ i * (X x i - μ i))^2) =
      ∑ i, ∑ j, μ i * μ j * C i j := by
    have hsq (x : Ω) : (∑ i, μ i * (X x i - μ i))^2 =
        ∑ i, ∑ j, μ i * μ j * ((X x i - μ i) * (X x j - μ j)) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hsq, expect_fintype_sum, expect_mul_left]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [C, μ]
    rw [covariance_centered]
  have hmain : P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) =
      (∑ i, ∑ j, 2 * (C i j + μ i * μ j) * C i j) / (n : ℝ)^2 := by
    simp_rw [dot_sub_right, dot_sq, expect_div, expect_fintype_sum,
      expect_mul_left, difference_product, expect_mul_right]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [C, covariance, μ]
    ring
  rw [hmain]
  change _ = (2 / (n : ℝ)^2) * ((∑ i, ∑ j, C i j ^ 2) + _)
  rw [hrem, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  rw [div_mul_eq_mul_div, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- decor:three-copy-bound for each finite conditional path law. -/
theorem three_copy_bound (X : Ω → Fin n → ℝ) :
    (2 / (n : ℝ)^2) *
      (∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j)^2) ≤
    P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) := by
  rw [P.three_copy_identity X]
  apply mul_le_mul_of_nonneg_left
  · exact le_add_of_nonneg_right (P.expect_nonneg (fun _ => sq_nonneg _))
  · positivity

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

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_Perturbations
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

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_path_expect (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f g : X → FinitePath Ω L → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y))
    (hg : ∀ y, Measurable (fun x => g x y)) :
    Measurable (fun x => (law L (tilt L T m (f x))).expect (g x)) := by
  induction L with
  | zero => simpa only [law_zero_expect] using hg ()
  | succ L ih =>
    simp_rw [law_succ_expect (Ω := Ω) L]
    exact T.1.measurable_tilt_expect (m 0)
      (fun a => measurable_backwardLog L (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)))
      (fun a => ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)) (fun b => hg (a,b)))

end DilutedSpinGlass.KernelTower

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

noncomputable local instance instDecidable_4_r9900be_1 (p : Prop) : Decidable p := Classical.propDecidable p
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

noncomputable local instance treeMarkLawPropDecidable_r9900be_1 (proposition : Prop) :
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ForkTree
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

lemma leaf_single_unique (n : ℕ) (a : (single n).Leaf) : a = singleLeaf n := by
  induction n with
  | zero => cases a; rfl
  | succ n ih =>
    rcases a with ⟨i,a⟩
    have hi := Fin.eq_zero i
    subst i
    exact congrArg (fun a : (single n).Leaf => (⟨0,a⟩ : (single (n+1)).Leaf)) (ih a)

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

theorem measurable_packRoot
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2)) :
    Measurable (packRoot F) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x => F z.1 k x z.2.1 z.2.2) (fun k => (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualNegligible
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree

lemma forkAtLeaf_surjective (n d : ℕ) (hd : d < n) : Function.Surjective (forkAtLeaf n d hd) := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero =>
      rintro ⟨i,a⟩
      refine ⟨i,?_⟩
      exact congrArg (fun a : (single n).Leaf => (⟨i,a⟩ : (forkAt (n+1) 0 hd).Leaf))
        (leaf_single_unique n a).symm
    | succ d =>
      rintro ⟨i,a⟩
      have hi := Fin.eq_zero i
      subst i
      obtain ⟨j,rfl⟩ := ih d (Nat.lt_of_succ_lt_succ hd) a
      exact ⟨j,rfl⟩

lemma forkAt_split (n d : ℕ) (hd : d < n) (i j : Fin 2) (hij : i ≠ j) :
    splitDepth (forkAt n d hd) (forkAtLeaf n d hd i) (forkAtLeaf n d hd j) = d := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero => exact splitDepth_diff_child (fun _ : Fin (2:ℕ+) => single n) i j hij _ _
    | succ d =>
      exact (splitDepth_same_child (fun _ : Fin (1:ℕ+) => forkAt n d (Nat.lt_of_succ_lt_succ hd))
        0 (forkAtLeaf n d _ i) (forkAtLeaf n d _ j)).trans (by rw [ih]; omega)

lemma forkAt_fresh (n d : ℕ) (hd : d < n) (i : Fin 2) :
    freshSplitDepth (forkAt n d hd) (forkAtVertex n d hd) (forkAtLeaf n d hd i) = d := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero => rfl
    | succ d =>
      exact (freshSplitDepth_same_child (fun _ : Fin (1:ℕ+) => forkAt n d (Nat.lt_of_succ_lt_succ hd))
        0 (forkAtVertex n d _) (forkAtLeaf n d _ i)).trans (by rw [ih]; omega)

lemma forkAt_gamma (n d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    gamma (forkAt n d hd) m (forkAtVertex n d hd) = m ⟨d,by omega⟩ - 2*m ⟨d+1,by omega⟩ := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero => rfl
    | succ d =>
      change gamma (forkAt n d _) (fun j => m j.succ) (forkAtVertex n d _) = _
      exact ih d (Nat.lt_of_succ_lt_succ hd) (fun j => m j.succ)

lemma forkAt_unique (n d : ℕ) (hd : d < n) (a : (forkAt n d hd).Leaf)
    (ha : splitDepth (forkAt n d hd) (forkAtLeaf n d hd 0) a = d) : a = forkAtLeaf n d hd 1 := by
  obtain ⟨i,rfl⟩ := forkAtLeaf_surjective n d hd a
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [splitDepth_self] at ha
    omega
  · rfl

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullThermalAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω] {N : ℕ}

lemma prefixEnergyAt_nonneg (n : ℕ) (T : KernelTower Ω n) (d : ℕ)
    (X : FinitePath Ω n → Fin N → ℝ) : 0 ≤ prefixEnergyAt n T d X := by
  induction n generalizing d with
  | zero => unfold prefixEnergyAt FiniteLaw.covarianceEnergy; positivity
  | succ n ih =>
    cases d with
    | zero => unfold prefixEnergyAt FiniteLaw.covarianceEnergy; positivity
    | succ d => exact T.1.expect_nonneg (fun z => ih (T.2 z) d (fun y => X (z,y)))

lemma prefix_three_copy_bound_at (n : ℕ) (T : KernelTower Ω n) (d : ℕ) (hd : d < n)
    (X : FinitePath Ω n → Fin N → ℝ) :
    2*prefixEnergyAt n T d X ≤ tripleExpectAt n T d
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero =>
      change 2*(law (n+1) T).covarianceEnergy X ≤ _
      have he : 2*(law (n+1) T).covarianceEnergy X =
          (2/(N:ℝ)^2)*(∑ i, ∑ j, (law (n+1) T).covariance (fun x => X x i) (fun x => X x j)^2) := by
        unfold FiniteLaw.covarianceEnergy
        ring
      rw [he]
      exact (law (n+1) T).three_copy_bound X
    | succ d =>
      change 2*T.1.expect _ ≤ T.1.expect _
      rw [← FiniteLaw.expect_mul_left]
      exact T.1.expect_mono (fun z => ih (T.2 z) d (by omega) (fun y => X (z,y)))

end DilutedSpinGlass.KernelTower
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
variable {Ω : Type} [Fintype Ω] {L : ℕ}

lemma shapeHistory_one (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (d : ℕ)
    (E D : FinitePath Ω (L+1) → ℝ) (f : Sample Ω S → ℝ) :
    shapeHistory T m (fun M : Option (Fin 1) → Option (Fin 1) → ℕ =>
        if M none (some 0) = d then 1 else 0)
      (fun c => match c with | none => E | some _ => D) S a f =
      pairHistory T m S a d E D f := by
  classical
  simp only [shapeHistory,List.ofFn_succ,List.ofFn_zero,List.reverse_cons,List.reverse_nil,
    List.nil_append,labeledHistory]
  unfold pairHistory
  congr 1
  · apply Finset.sum_congr rfl
    intro b hb
    simp only [Fintype.prod_option,Fin.prod_univ_one,Function.update_of_ne (by simp : (none : Option (Fin 1)) ≠ some 0),Function.update_self,id_eq]
    split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro v _
    simp only [Fintype.prod_option,Fin.prod_univ_one,Function.update_of_ne (by simp : (none : Option (Fin 1)) ≠ some 0),Function.update_self]
    split_ifs <;> simp

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

noncomputable local instance pairObservableHistoryDecidable_r9900be_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma pairObservableHistory_product {L : ℕ} (T : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ) (S : PrescribedTree (L+1)) (a : S.Leaf) (d : ℕ)
    (E D : FinitePath Ω (L+1) → ℝ) (f : Sample Ω S → ℝ) :
    pairObservableHistory T m S a d (fun x y => E x*D y) f = pairHistory T m S a d E D f := rfl

lemma pair_univ_erase (S : PrescribedTree n) (a : S.Leaf) (d : ℕ) (hd : d < n) :
    (∑ b ∈ Finset.univ.erase a, if splitDepth S a b = d then (1:ℝ) else 0) =
      ∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0 := by
  classical
  have he := Finset.sum_erase_add (Finset.univ : Finset S.Leaf)
    (fun b => if splitDepth S a b = d then (1:ℝ) else 0) (Finset.mem_univ a)
  simpa only [splitDepth_self,ite_eq_right (Ne.symm (Nat.ne_of_lt hd)),add_zero] using he

/-- Exact, old-tree-independent singleton-anchor coefficient at a fixed split. -/
theorem pairObservableHistory_const (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (R : FinitePath Ω n → FinitePath Ω n → ℝ) :
    pairObservableHistory T m S a d R (fun _ => 1) =
      (m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩) * KernelTower.pairExpect n T d R := by
  classical
  unfold pairObservableHistory
  simp only [one_mul]
  have ho (b : S.Leaf) :
      (if splitDepth S a b = d then
        (S.sampleLaw T).expect (fun x => R (S.pathAt a x) (S.pathAt b x)) else 0) =
      (if splitDepth S a b = d then (1:ℝ) else 0)*KernelTower.pairExpect n T d R := by
    split_ifs with hb
    · rw [pair_marginal,hb,one_mul]
    · simp
  have hv (v : S.Internal) :
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw T).expect (fun x => R
          ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0) =
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then gamma S m v else 0)*
        KernelTower.pairExpect n T d R := by
    split_ifs with hv
    · rw [pair_marginal,hv]
    · simp
  simp_rw [ho,hv]
  rw [← Finset.sum_mul,← Finset.sum_mul,← add_mul,pair_univ_erase S a d hd,
    pair_choice_total S a d hd m hend]

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
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

noncomputable local instance pairSiteAverageDecidable_r9900be_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma pairObservableHistory_sum {ι : Type*} (I : Finset ι)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : ι → FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) :
    pairObservableHistory T m S a d (fun x y => ∑ i ∈ I, R i x y) f =
      ∑ i ∈ I, pairObservableHistory T m S a d (R i) f := by
  classical
  unfold pairObservableHistory
  simp only [Finset.mul_sum,FiniteLaw.expect_sum,Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs <;> simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> simp

lemma pairObservableHistory_div
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) (c : ℝ) :
    pairObservableHistory T m S a d (fun x y => R x y/c) f =
      pairObservableHistory T m S a d R f/c := by
  unfold pairObservableHistory
  simp only [← mul_div_assoc,FiniteLaw.expect_div,add_div,Finset.sum_div]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro v hv <;> split_ifs <;> simp

/-- The empirical overlap is the physical iid-uniform site average of the
literal one-color histories. No independence from the old test is imposed. -/
theorem pair_history_dot (T : KernelTower Ω (n+1)) (m : Fin (n+2) → ℝ)
    (S : PrescribedTree (n+1)) (a : S.Leaf) (d : ℕ)
    (X : FinitePath Ω (n+1) → Fin N → ℝ) (f : Sample Ω S → ℝ) :
    pairObservableHistory T m S a d (fun x y => FiniteLaw.dot (X x) (X y)) f =
      (∑ i : Fin N, shapeHistory T m
        (fun M : Option (Fin 1) → Option (Fin 1) → ℕ => if M none (some 0) = d then 1 else 0)
        (fun _ x => X x i) S a f)/(N:ℝ) := by
  unfold FiniteLaw.dot
  rw [pairObservableHistory_div,pairObservableHistory_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact (shapeHistory_one T m S a d (fun x => X x i) (fun x => X x i) f).symm

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance pairSquareDecidable_r9900be_1 (proposition : Prop) :
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeMeasurable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

/-- Measurability of every finite prescribed-tree probability for the actual
recursively tilted conditional kernels. -/
theorem measurable_tilt_sample_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (a : S.Sample Ω) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).weight a) := by
  induction S with
  | leaf => exact measurable_const
  | @node n k C ih =>
    change Measurable (fun x => ∏ i : Fin k,
      (T.1.tilt (m 0) (fun z => KernelTower.backwardLog n (T.2 z)
        (fun j => m j.succ) (fun y => f x (z,y)))).weight (a i).1 *
      ((C i).sampleLaw (KernelTower.tilt n (T.2 (a i).1)
        (fun j => m j.succ) (fun y => f x ((a i).1,y)))).weight (a i).2)
    apply Finset.measurable_prod
    intro i _
    exact (T.1.measurable_tilt_weight (m 0)
      (fun z => KernelTower.measurable_backwardLog n (T.2 z) (fun j => m j.succ)
        (fun y => hf (z,y))) (a i).1).mul
      (ih i (T.2 (a i).1) (fun j => m j.succ) (fun y => hf ((a i).1,y)) (a i).2)

theorem measurable_tilt_sample_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    {g : X → S.Sample Ω → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (hg : ∀ a, Measurable (fun x => g x a)) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).expect (g x)) := by
  apply Finset.measurable_sum
  intro a _
  exact (measurable_tilt_sample_weight S T m hf a).mul (hg a)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullTreeScore
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {L : ℕ}
lemma shapeHistory_pair (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (d : ℕ)
    (D : FinitePath Ω (L+1) → ℝ) (f : Sample Ω S → ℝ) :
    shapeHistory T m (fun B : Option (Fin 1) → Option (Fin 1) → ℕ => if B none (some 0) = d then 1 else 0)
      (fun c x => match c with | none => if true = true then D x else 1 | some _ => D x) S a f =
      pairObservableHistory T m S a d (fun x y => D x * D y) f := by
  have hcol : (fun (c : Option (Fin 1)) x => match c with | none => if true = true then D x else 1 | some _ => D x) =
      (fun c => match c with | none => D | some _ => D) := by
    funext c x; cases c <;> rfl
  rw [hcol]
  exact (shapeHistory_one T m S a d D D f).trans (pairObservableHistory_product T m S a d D D f).symm
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

noncomputable local instance generalPairSquareDecidable_r9900be_1 (proposition : Prop) :
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
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n : ℕ}

noncomputable local instance matrixPairRegularityPropDecidable_r9900be_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
lemma measurable_pairObservableHistory_tilt
    (T : KernelTower Ω n) (m : Fin n → ℝ) (exponents : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    {g : Z → FinitePath Ω n → ℝ}
    {R : Z → FinitePath Ω n → FinitePath Ω n → ℝ} {f : Z → Sample Ω S → ℝ}
    (hg : ∀ x, Measurable (fun z => g z x)) (hR : ∀ x y, Measurable (fun z => R z x y))
    (hf : ∀ x, Measurable (fun z => f z x)) :
    Measurable (fun z => pairObservableHistory (KernelTower.tilt n T m (g z)) exponents S a d (R z) (f z)) := by
  unfold pairObservableHistory
  apply Measurable.add
  · apply Finset.measurable_sum; intro b _
    split_ifs
    · exact measurable_tilt_sample_expect S T m hg (fun x => (hf x).mul (hR _ _))
    · exact measurable_const
  · apply Finset.measurable_sum; intro v _
    split_ifs
    · exact (measurable_tilt_sample_expect (grow S v) T m hg
        (fun x => (hf _).mul (hR _ _))).const_mul _
    · exact measurable_const

lemma pairObservableHistory_bound (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ x y, |R x y| ≤ 1) (hf : ∀ x, |f x| ≤ B) :
    |pairObservableHistory T m S a d R f| ≤ pairHistoryMass S m a*B := by
  have hp (x : Sample Ω S) (y z) : |f x*R y z| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hf x) (hR y z) (abs_nonneg _) hB).trans_eq (mul_one B)
  unfold pairObservableHistory pairHistoryMass
  calc
    _ ≤ (∑ b ∈ (Finset.univ : Finset S.Leaf).erase a,
      |if splitDepth S a b = d then (S.sampleLaw T).expect (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) else 0|) +
      ∑ v : S.Internal, |if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw T).expect (fun x => f (oldSample S v x)*
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (∑ _b ∈ (Finset.univ : Finset S.Leaf).erase a, B) + ∑ v : S.Internal, |gamma S m v| *B := by
      apply add_le_add
      · apply Finset.sum_le_sum; intro b _
        split_ifs
        · exact FiniteLaw.abs_expect_le _ (fun x => hp x _ _)
        · simpa using hB
      · apply Finset.sum_le_sum; intro v _
        split_ifs
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (FiniteLaw.abs_expect_le _ (fun x => hp _ _ _)) (abs_nonneg _)
        · simpa using mul_nonneg (abs_nonneg (gamma S m v)) hB
    _ = _ := by simp [← Finset.sum_mul,add_mul]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
theorem general_decorrelation_bound_at (n d : ℕ) (hd : d < n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1)
    (S : PrescribedTree n) (a b : S.Leaf) (v : S.Internal)
    (hab : splitDepth S a b = d)
    (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (X : FinitePath Ω n → Fin N → ℝ)
    (hOld : ∀ c, splitDepth S a c = d → ∀ x : Sample Ω S,
      X (S.pathAt c x) = X (S.pathAt b x)) :
    (-gamma S m v)*KernelTower.prefixEnergyAt n T d X ≤
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
  have h3 := KernelTower.prefix_three_copy_bound_at n T d hd X
  rw [← hD] at h3
  have hmul := mul_le_mul_of_nonneg_left h3 (pairFreshCost_nonneg S m hm hp a d v)
  rw [hcost] at hmul hone
  change (1/2:ℝ)*(∑ w : S.Internal, pairFreshCost S m a d w * D w) = _ at hsum
  linarith


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

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0) (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma measurable_rootTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (rootTreeMean S T Q m base old f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootTreeMean_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |rootTreeMean S T Q m base old f z| ≤ B :=
  FiniteLaw.abs_expect_le _ (fun _ => hf _)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MeasurableEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma measurable_covarianceEnergy_tilt (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {f : Z → FinitePath Ω n → ℝ} {X : Z → FinitePath Ω n → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => (law n (tilt n T m (f z))).covarianceEnergy (X z)) := by
  unfold FiniteLaw.covarianceEnergy FiniteLaw.covariance
  apply Measurable.div_const
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  exact (measurable_path_expect n T m hf (fun y => (hX y i).mul (hX y j))).sub
    ((measurable_path_expect n T m hf (fun y => hX y i)).mul
      (measurable_path_expect n T m hf (fun y => hX y j)))

lemma measurable_prefixEnergyAt_tilt (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (d : ℕ) {f : Z → FinitePath Ω n → ℝ} {X : Z → FinitePath Ω n → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => prefixEnergyAt n (tilt n T m (f z)) d (X z)) := by
  induction n generalizing d with
  | zero => exact measurable_covarianceEnergy_tilt 0 T m hf hX
  | succ n ih =>
    cases d with
    | zero => exact measurable_covarianceEnergy_tilt (n+1) T m hf hX
    | succ d =>
      apply T.1.measurable_tilt_expect (m 0)
      · intro a
        exact measurable_backwardLog n (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
      · intro a
        exact ih (T.2 a) (fun j => m j.succ) d (fun y => hf (a,y)) (fun y i => hX (a,y) i)

lemma prefixEnergyAt_le_two (n : ℕ) (T : KernelTower Ω n) (d : ℕ) (hd : d < n)
    (X : FinitePath Ω n → Fin N → ℝ) (hX : ∀ x i, |X x i| ≤ 1) :
    prefixEnergyAt n T d X ≤ 2 := by
  have h3 := prefix_three_copy_bound_at n T d hd X
  have hb : tripleExpectAt n T d
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) ≤ 4 := by
    clear h3
    induction n generalizing d with
    | zero => omega
    | succ n ih =>
      cases d with
      | zero =>
        change (law (n+1) T).expect _ ≤ _
        calc
          _ ≤ (law (n+1) T).expect (fun _ => (4:ℝ)) := by
            apply FiniteLaw.expect_mono; intro x
            calc
              _ ≤ (law (n+1) T).expect (fun _ => (4:ℝ)) := by
                apply FiniteLaw.expect_mono; intro y
                calc
                  _ ≤ (law (n+1) T).expect (fun _ => (4:ℝ)) := by
                    apply FiniteLaw.expect_mono; intro z
                    have ha := FiniteLaw.abs_dot_le_one (X x) (X y) (hX x) (hX y)
                    have hb := FiniteLaw.abs_dot_le_one (X x) (X z) (hX x) (hX z)
                    rcases abs_le.mp ha with ⟨ha,ha'⟩
                    rcases abs_le.mp hb with ⟨hb,hb'⟩
                    nlinarith [sq_nonneg (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))]
                  _ = _ := FiniteLaw.expect_const _ _
              _ = _ := FiniteLaw.expect_const _ _
          _ = _ := FiniteLaw.expect_const _ _
      | succ d =>
        exact (T.1.expect_mono (fun z => ih (T.2 z) d (by omega) (fun y => X (z,y))
          (fun y i => hX (z,y) i))).trans_eq (T.1.expect_const 4)
  linarith

end DilutedSpinGlass.KernelTower
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ParameterRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (d : ℕ) (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootConditionalEnergy : Measurable (rootConditionalEnergy T Q m base old d V) := by
  change Measurable (packRoot (fun h k x n y =>
    KernelTower.prefixEnergyAt L
      (KernelTower.tilt L (tower (rootArray n y) L T Q) m (logWeight (base h k x) (rootArray n y) old))
      d (fun w => V (physical (rootArray n y) L w))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  exact KernelTower.measurable_prefixEnergyAt_tilt L (tower (rootArray n y) L T Q) m d
    (fun w => (hb k _).add measurable_const) (fun _ _ => measurable_const)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootConditionalEnergy_bound (hd : d < L) (hV : ∀ x i, |V x i| ≤ 1)
    (z : FullRootState Y X I M) : |rootConditionalEnergy T Q m base old d V z| ≤ 2 := by
  rw [rootConditionalEnergy,abs_of_nonneg (KernelTower.prefixEnergyAt_nonneg _ _ _ _)]
  exact KernelTower.prefixEnergyAt_le_two L _ d hd _ (fun x i => hV _ i)

include hb in
lemma integrable_rootConditionalEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hd : d < L) (hV : ∀ x i, |V x i| ≤ 1) :
    Integrable (rootConditionalEnergy T Q m base old d V) μ := by
  apply Integrable.of_bound (measurable_rootConditionalEnergy T Q m base old d V hb).aestronglyMeasurable 2
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using (rootConditionalEnergy_bound T Q m base old d V hd hV z))

include hb in
lemma integrable_rootTreeMean (S : PrescribedTree L) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    {B : ℝ} (hf : ∀ x, |f x| ≤ B) : Integrable (rootTreeMean S T Q m base old f) μ := by
  apply Integrable.of_bound (measurable_rootTreeMean S T Q m base old f hb).aestronglyMeasurable B
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using (rootTreeMean_bound S T Q m base old f hf z))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UniformRootDecorrelation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (n d N : ℕ)
    (T : (z : Z) → KernelTower (Ω z) n)
    (X : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (m : Fin (n+1) → ℝ) (S : PrescribedTree n) (a b : S.Leaf)

omit [IsProbabilityMeasure μ] in
lemma pairRootCovariance_center (hd : d < n) (hab : splitDepth S a b = d)
    (hend : m (Fin.last n) = 1) :
    pairRootCovariance μ Ω n d N T X m S a b =
      (∫ z, pairObservableHistory (T z) m S a d
        (fun x y => FiniteLaw.dot (X z x) (X z y))
        (fun x => FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))) ∂μ) +
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)*(pairRootMean μ Ω n N T X S a b)^2 := by
  unfold pairRootCovariance
  have he (z : Z) := pairObservableHistory_const (T z) m hend S a d hd
    (fun x y => FiniteLaw.dot (X z x) (X z y))
  have hmarg (z : Z) : KernelTower.pairExpect n (T z) d
      (fun x y => FiniteLaw.dot (X z x) (X z y)) =
      (S.sampleLaw (T z)).expect (fun x => FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))) := by
    have q := pair_marginal S (T z) a b (fun x y => FiniteLaw.dot (X z x) (X z y))
    rw [hab] at q
    exact q.symm
  simp_rw [he,hmarg]
  rw [integral_const_mul]
  change _ - pairRootMean μ Ω n N T X S a b *
    ((m ⟨d,by omega⟩-m ⟨d+1,by omega⟩)*pairRootMean μ Ω n N T X S a b) = _
  ring

/-- The single-copy conditional covariance estimate with the exact shared
root covariance. Applicability is to arbitrary old trees, not surrogate laws. -/
theorem root_decorrelation_bound (hd : d < n) (hab : splitDepth S a b = d)
    (v : S.Internal) (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (hX : ∀ z x i, |X z x i| ≤ 1)
    (hOld : ∀ z c, splitDepth S a c = d → ∀ x : Sample (Ω z) S,
      X z (S.pathAt c x) = X z (S.pathAt b x))
    (hE : Integrable (fun z => KernelTower.prefixEnergyAt n (T z) d (X z)) μ)
    (hA : Integrable (fun z => (S.sampleLaw (T z)).expect (fun x =>
      FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))^2)) μ)
    (hH : Integrable (fun z => pairObservableHistory (T z) m S a d
      (fun x y => FiniteLaw.dot (X z x) (X z y))
      (fun x => FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x)))) μ) :
    (-gamma S m v)*(∫ z, KernelTower.prefixEnergyAt n (T z) d (X z) ∂μ) ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) + pairRootCovariance μ Ω n d N T X m S a b := by
  have hi := integral_mono (hE.const_mul (-gamma S m v))
    ((hA.const_mul (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)).add hH)
    (fun z => general_decorrelation_bound_at n d hd (T z) m hm hp hend S a b v hab hav hbv
      (X z) (hOld z))
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (hA.const_mul _) hH,integral_const_mul] at hi
  rw [pairRootCovariance_center μ Ω n d N T X m S a b hd hab hend]
  have hAone : (∫ z, (S.sampleLaw (T z)).expect (fun x =>
      FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))^2) ∂μ) ≤ 1 := by
    calc
      _ ≤ ∫ _z : Z, (1:ℝ) ∂μ := integral_mono hA (integrable_const 1) (fun z => by
        calc
          _ ≤ (S.sampleLaw (T z)).expect (fun _ => (1:ℝ)) :=
            FiniteLaw.expect_mono _ (fun x => (sq_le_one_iff_abs_le_one _).mpr
              (FiniteLaw.abs_dot_le_one _ _ (hX z _) (hX z _)))
          _ = _ := FiniteLaw.expect_const _ _)
      _ = 1 := by simp
  have hδ : 0 ≤ m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ := sub_nonneg.mpr (hm (by simp))
  have hv := mul_nonneg hδ (sq_nonneg (pairRootMean μ Ω n N T X S a b))
  have hs := mul_le_mul_of_nonneg_left hAone hδ
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExternalTaylor
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (S : PrescribedTree L) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω L → FinitePath Ω L → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootPairObservable : Measurable (rootPairObservable T Q m base old S a d R f) := by
  change Measurable (packRoot (fun h k x n y => pairObservableHistory
    (KernelTower.tilt L (tower (rootArray n y) L T Q) (fun j => m j.succ)
      (logWeight (base h k x) (rootArray n y) old)) m S a d
    (fun x y' => R (physical (rootArray n y) L x) (physical (rootArray n y) L y'))
    (fun x => f (fun b => physical (rootArray n y) L (S.pathAt b x)))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  exact measurable_pairObservableHistory_tilt (tower (rootArray n y) L T Q) (fun j => m j.succ)
    m S a d (fun w => (hb k _).add measurable_const) (fun _ _ => measurable_const)
    (fun _ => measurable_const)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootPairObservable_bound {B : ℝ} (hB : 0 ≤ B)
    (hR : ∀ x y, |R x y| ≤ 1) (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |rootPairObservable T Q m base old S a d R f z| ≤ pairHistoryMass S m a*B :=
  pairObservableHistory_bound _ m S a d _ _ hB (fun _ _ => hR _ _) (fun _ => hf _)

include hb in
lemma integrable_rootPairObservable (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ x y, |R x y| ≤ 1) (hf : ∀ x, |f x| ≤ B) :
    Integrable (rootPairObservable T Q m base old S a d R f) μ := by
  apply Integrable.of_bound (measurable_rootPairObservable T Q m base old S a d R f hb).aestronglyMeasurable
    (pairHistoryMass S m a*B)
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using (rootPairObservable_bound T Q m base old S a d R f hB hR hf z))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExternalRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (S : PrescribedTree L) (a b : S.Leaf) (d : ℕ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ x i, |V x i| ≤ 1)
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
include hb hV

lemma integrable_rootPair_square : Integrable (fun z =>
    (S.sampleLaw (rootTower T Q (fun j => m j.succ) base old z)).expect (fun x =>
      FiniteLaw.dot (rootVector V z (S.pathAt a x)) (rootVector V z (S.pathAt b x))^2)) μ := by
  apply integrable_rootTreeMean T Q (fun j => m j.succ) base old hb S
    (fun x => FiniteLaw.dot (V (x a)) (V (x b))^2) μ
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr (FiniteLaw.abs_dot_le_one _ _ (hV _) (hV _))

lemma integrable_rootPair_history : Integrable (fun z =>
    pairObservableHistory (rootTower T Q (fun j => m j.succ) base old z) m S a d
      (fun x y => FiniteLaw.dot (rootVector V z x) (rootVector V z y))
      (fun x => FiniteLaw.dot (rootVector V z (S.pathAt a x)) (rootVector V z (S.pathAt b x)))) μ := by
  exact integrable_rootPairObservable T Q m base old S a d
    (fun x y => FiniteLaw.dot (V x) (V y)) (fun x => FiniteLaw.dot (V (x a)) (V (x b)))
    hb μ (by norm_num : (0:ℝ) ≤ 1)
    (fun x y => FiniteLaw.abs_dot_le_one _ _ (hV x) (hV y))
    (fun x => FiniteLaw.abs_dot_le_one _ _ (hV _) (hV _))

/-- Nonnegative three-copy control for the actual random-reservoir root law.
No integrability side conditions or covariance estimates are assumed. -/
theorem root_model_decorrelation_bound (hd : d < L) (hab : splitDepth S a b = d)
    (v : S.Internal) (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (huniq : ∀ c, splitDepth S a c = d → c = b)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last L) = 1) :
    (-gamma S m v)*(∫ z, rootConditionalEnergy T Q (fun j => m j.succ) base old d V z ∂μ) ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
      pairRootCovariance μ (rootAlphabet (Ω := Ω) (A := A)) L d N
        (rootTower T Q (fun j => m j.succ) base old) (rootVector V) m S a b := by
  apply root_decorrelation_bound μ (rootAlphabet (Ω := Ω) (A := A)) L d N
    (rootTower T Q (fun j => m j.succ) base old) (rootVector V) m S a b hd hab v hav hbv hm hp hend
  · intro z x i; exact hV _ i
  · intro z c hc x; rw [huniq c hc]
  · exact integrable_rootConditionalEnergy T Q (fun j => m j.succ) base old d V hb μ hd hV
  · exact integrable_rootPair_square T Q m base old S a b V hb hV μ
  · exact integrable_rootPair_history T Q m base old S a b d V hb hV μ

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_VertexContinuity
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot Filter Set
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

lemma exponent_cons_monotone (hm : ∀ l, 0 ≤ m l) (hmono : Monotone m) : Monotone (Fin.cons 0 m) := by
  exact monotone_vecCons.mpr ⟨hm 0,hmono⟩

lemma exponent_cons_nonneg (hm : ∀ l, 0 ≤ m l) : ∀ l : Fin (L+2), 0 ≤ (Fin.cons 0 m : Fin (L+2) → ℝ) l := by
  intro l
  exact Fin.cases (by simp) (fun l => by simpa only [Fin.cons_succ] using hm l) l

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalPairConnection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory
open scoped BigOperators
lemma integral_siteLaw (N : ℕ) (f : Site N → ℝ) :
    (∫ i, f i ∂siteLaw N) = (∑ i, f i)/(max N 1:ℕ) := by
  rw [siteLaw,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,Fintype.card_fin]
  simp only [div_eq_mul_inv,Finset.sum_mul,mul_comm]
end DilutedSpinGlass.ConcreteReservoir

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

omit [Fintype Ω] in
lemma readVector_bound (read : Site N → FinitePath Ω (L+1) → Spin) (x) (i) :
    |readVector read x i| ≤ 1 := by simp only [readVector,abs_spin,le_refl]

variable (S : PrescribedTree (L+1)) (a : S.Leaf) (T : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin) (d : ℕ)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootShapeHistory_pair (z : FullRootState Y X (Labels L (Site N)) M) (v : Site N) :
    rootShapeHistory S a T m base old read (pairSplitTest d) true f z v =
      rootPairObservable T (fun i => prior i.1.1) m base old S a d
        (fun x y => spin (read v x)*spin (read v y)) f z := by
  exact shapeHistory_pair
    (rootTower T (fun i => prior i.1.1) (fun j => m j.succ) base old z) m S a d
    (fun x => spin (read v (physical (rootArray z.2.2.1 z.2.2.2) (L+1) x)))
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma integral_rootShapeHistory_pair (z : FullRootState Y X (Labels L (Site N)) M) :
    (∫ i, rootShapeHistory S a T m base old read (pairSplitTest d) true f z i ∂siteLaw N) =
      rootPairObservable T (fun i => prior i.1.1) m base old S a d
        (fun x y => FiniteLaw.dot (readVector read x) (readVector read y)) f z := by
  rw [integral_siteLaw]
  symm
  exact pair_history_dot (rootTower T (fun i => prior i.1.1) (fun j => m j.succ) base old z)
    m S a d (rootVector (readVector read) z)
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
include hb hB hf

omit hB hf in
lemma measurable_rootShapeHistory_pair_slice (v : Site N) :
    Measurable (fun z => rootShapeHistory S a T m base old read (pairSplitTest d) true f z v) := by
  have h := measurable_rootPairObservable T (fun i => prior i.1.1) m base old S a d
    (fun x y => spin (read v x)*spin (read v y)) f hb
  have he : rootPairObservable T (fun i => prior i.1.1) m base old S a d
      (fun x y => spin (read v x)*spin (read v y)) f =
      (fun z => rootShapeHistory S a T m base old read (pairSplitTest d) true f z v) :=
    funext (fun z => (rootShapeHistory_pair S a T m base old read d f z v).symm)
  exact he ▸ h

omit hB hf in
lemma measurable_rootShapeHistory_pair : Measurable (fun z : FullRootState Y X (Labels L (Site N)) M × Site N =>
      rootShapeHistory S a T m base old read (pairSplitTest d) true f z.1 z.2) := by
  exact measurable_from_prod_countable_left
    (fun i => measurable_rootShapeHistory_pair_slice S a T m base old read d f hb i)

omit hb [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootShapeHistory_pair_bound (z : FullRootState Y X (Labels L (Site N)) M) (v : Site N) :
    |rootShapeHistory S a T m base old read (pairSplitTest d) true f z v| ≤ pairHistoryMass S m a*B := by
  rw [rootShapeHistory_pair S a T m base old read d f z v]
  apply rootPairObservable_bound T (fun i => prior i.1.1) m base old S a d _ f hB _ hf
  intro x y
  simp only [abs_mul,abs_spin,mul_one,le_refl]

lemma integrable_rootShapeHistory_pair (μ : Measure (FullRootState Y X (Labels L (Site N)) M))
    [IsFiniteMeasure μ] :
    Integrable (fun z : FullRootState Y X (Labels L (Site N)) M × Site N =>
      rootShapeHistory S a T m base old read (pairSplitTest d) true f z.1 z.2) (μ.prod (siteLaw N)) := by
  apply Integrable.of_bound (measurable_rootShapeHistory_pair S a T m base old read d f hb).aestronglyMeasurable
    (pairHistoryMass S m a*B)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs]
  exact rootShapeHistory_pair_bound S a T m base old read d f hB hf z.1 z.2

lemma shapeAverage_pair (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) :
    shapeAverage ξ μ ν (siteLaw N) rate score S a T m base old read (pairSplitTest d) true f =
      ∫ z, rootPairObservable T (fun i => prior i.1.1) m base old S a d
        (fun x y => FiniteLaw.dot (readVector read x) (readVector read y)) f z
        ∂fullRootLaw ξ μ ν rate score := by
  unfold shapeAverage
  rw [integral_prod _ (integrable_rootShapeHistory_pair S a T m base old read d f hb hB hf
    (fullRootLaw ξ μ ν rate score))]
  exact integral_congr_ae (ae_of_all _ (fun z => integral_rootShapeHistory_pair S a T m base old read d f z))

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalPairEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

omit [Fintype Ω] in
lemma pairOverlap_bound (S : PrescribedTree (L+1)) (a b : S.Leaf)
    (read : Site N → FinitePath Ω (L+1) → Spin) (x) : |pairOverlap S a b read x| ≤ 1 :=
  FiniteLaw.abs_dot_le_one _ _ (readVector_bound read _) (readVector_bound read _)

variable (S : PrescribedTree (L+1)) (a b : S.Leaf) (T : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin) (d : ℕ)
    (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0)
include hb

lemma shapeCovariance_pair :
    shapeCovariance ξ μ ν (siteLaw N) rate score S a T m base old read (pairSplitTest d) true
      (pairOverlap S a b read) =
    pairRootCovariance (fullRootLaw ξ μ ν rate score)
      (rootAlphabet (Ω := Ω) (A := fun i : Labels L (Site N) => Alphabet i.1.1))
      (L+1) d (max N 1) (rootTower T (fun i => prior i.1.1) (fun j => m j.succ) base old)
      (rootVector (readVector read)) m S a b := by
  unfold shapeCovariance
  rw [shapeAverage_pair S a T m base old read d _ hb (by norm_num : (0:ℝ) ≤ 1)
      (pairOverlap_bound S a b read) ξ μ ν rate score,
    shapeAverage_pair S a T m base old read d _ hb (by norm_num : (0:ℝ) ≤ 1)
      (fun _ => by simp : ∀ _, |(1:ℝ)| ≤ 1) ξ μ ν rate score]
  rfl

/-- Physical singleton covariance bound. The only tree assumptions here are
positional: exactly one eligible second leaf, and an actual common fork. All
root integrability obligations are discharged for the true reservoir. -/
theorem shape_energy_bound (hd : d < L+1) (hab : splitDepth S a b = d)
    (v : S.Internal) (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (huniq : ∀ c, splitDepth S a c = d → c = b)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last (L+1)) = 1) :
    (-gamma S m v) * (∫ z,
      rootConditionalEnergy T (fun i => prior i.1.1) (fun j => m j.succ) base old d (readVector read) z
        ∂fullRootLaw ξ μ ν rate score) ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
      shapeCovariance ξ μ ν (siteLaw N) rate score S a T m base old read (pairSplitTest d) true
        (pairOverlap S a b read) := by
  have hi := root_model_decorrelation_bound T (fun i => prior i.1.1) m base old S a b d
    (readVector read) hb (readVector_bound read) (fullRootLaw ξ μ ν rate score)
    hd hab v hav hbv huniq hm hp hend
  have he := shapeCovariance_pair S a b T m base old read d hb ξ μ ν rate score
  exact hi.trans_eq (congrArg (fun x => (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+x) he.symm)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalSingleton
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

lemma singletonOldTest_bound (d : ℕ) (hd : d < L+1) (N : ℕ) (x) :
    |singletonOldTest d hd N x| ≤ 1 := pairOverlap_bound _ _ _ _ _

/-- Exact one-color singleton estimate at every N, before taking any limit.
The error is the literal physical prescribed-shape covariance already selected
by the universal perturbation, not a newly imposed covariance hypothesis. -/
theorem physical_singleton_bound (m : Fin (L+1) → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ) (d : ℕ) (hd : d < L+1) :
    (2*(Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-(Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d,by omega⟩) *
      physicalSingletonEnergy m M C H N u d ≤
    ((Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-(Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d,by omega⟩) +
      physicalShapeCovariance m (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0)
        M C H N u (pairSplitTest d) true (singletonOldTest d hd N) := by
  have h := shape_energy_bound (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0)
    (forkAtLeaf (L+1) d hd 1)
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) d
    (measurable_physicalBase M C H N)
    (fun _ : Fin N => M.field.toMeasure) (bondLaw M N) (markLaw (weights L) N)
    (M.alpha*N) (scoreRate N) hd (forkAt_split (L+1) d hd 0 1 (by decide))
    (forkAtVertex (L+1) d hd) (forkAt_fresh (L+1) d hd 0) (forkAt_fresh (L+1) d hd 1)
    (fun c hc => forkAt_unique (L+1) d hd c hc)
    (exponent_cons_monotone m hm hmono) (exponent_cons_nonneg m hm) (by simpa using hend)
  rw [forkAt_gamma] at h
  simp only [neg_sub] at h
  exact h

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullCubeConditionalContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

lemma gridExponents_cons (L : ℕ) :
    Fin.cons 0 (gridExponents L) = grid (L+1) 0 (L+1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [grid]
  · simp [grid,gridExponents,Fin.val_succ]

lemma gridExponents_lower (L : ℕ) (j : Fin (L+1)) :
    ((L+1:ℕ):ℝ)⁻¹ ≤ gridExponents L j := by
  change _ ≤ (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Nat.le_add_left 1 j.val)

lemma gridExponents_mono (L : ℕ) : Monotone (gridExponents L) := by
  intro i j hij
  change (((i:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ) ≤ (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hij 1) (Nat.cast_nonneg _)

lemma gridExponents_last (L : ℕ) : gridExponents L (Fin.last L) = 1 := by
  simp only [gridExponents,Fin.val_last]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos L)))

lemma physicalSingletonEnergy_nonneg (m : Fin (L+1) → ℝ) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (d : ℕ) : 0 ≤ physicalSingletonEnergy m M C H N u d := by
  apply integral_nonneg
  intro z
  exact KernelTower.prefixEnergyAt_nonneg _ _ _ _

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullRegularSelection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable local instance fullRegularSelectionDecidableEq_r9900be_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

lemma FullShapeControl.singleton_energy {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (d : ℕ) (hd : d<L+1) {t : ℝ} (ht : 0<t) :
    ∀ᶠ n in atTop,
      (2*(Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-
        (Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) ⟨d,by omega⟩) *
        physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d ≤
      ((Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-
        (Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) ⟨d,by omega⟩)+t := by
  have hlim := h.shape (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0)
    (fun n => singletonOldTest d hd (Ns n+1)) 1 (by norm_num)
    (fun n x => singletonOldTest_bound d hd (Ns n+1) x) 1 (pairSplitTest d) true
  have hsmall : ∀ᶠ n in atTop, physicalShapeCovariance (gridExponents L) (forkAt (L+1) d hd)
      (forkAtLeaf (L+1) d hd 0) M C H (Ns n+1) (us n) (pairSplitTest d) true
      (singletonOldTest d hd (Ns n+1)) < t := (tendsto_order.1 hlim).2 t ht
  filter_upwards [hsmall] with n hn
  exact (physical_singleton_bound (gridExponents L) (fun j => (gridExponents_pos L j).le)
    (gridExponents_mono L) (gridExponents_last L) M C H (Ns n+1) (us n) d hd).trans
    (add_le_add le_rfl hn.le)

lemma FullShapeControl.singleton_regular_sat_oai {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    {η t : ℝ} (hη : 0<η) (ht : 0<t) : ∀ᶠ n in atTop,
    ∀ d ∈ regularSingletonDepths L η,
      physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d≤((L+1:ℕ):ℝ)⁻¹/η+t := by
  apply (Filter.eventually_all_finset _).mpr
  intro d hd
  have hreg := (Finset.mem_filter.mp hd).2.1
  have hs := h.singleton_energy d d.isLt (mul_pos hη ht)
  filter_upwards [hs] with n hn
  rw [gridExponents_cons] at hn
  have hcoef : η≤2*grid (L+1) 0 (L+1) ⟨d.val+1,by omega⟩-
      grid (L+1) 0 (L+1) ⟨d.val,by omega⟩ := by
    simp only [grid,Nat.zero_add,Nat.cast_add,Nat.cast_one,add_div]
    have hx : 0≤(1:ℝ)/((L+1:ℕ):ℝ) := by positivity
    change η<(d.val:ℝ)/((L+1:ℕ):ℝ) at hreg
    simp only [Nat.cast_add,Nat.cast_one] at hreg hx
    linarith
  have hstep : grid (L+1) 0 (L+1) ⟨d.val+1,by omega⟩-
      grid (L+1) 0 (L+1) ⟨d.val,by omega⟩=((L+1:ℕ):ℝ)⁻¹ := by
    simp [grid,Nat.cast_add,add_div]
  rw [hstep] at hn
  have hen := physicalSingletonEnergy_nonneg (gridExponents L) M C H (Ns n+1) (us n) d
  have hx : η*physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d≤
      ((L+1:ℕ):ℝ)⁻¹+η*t := (mul_le_mul_of_nonneg_right hcoef hen).trans hn
  calc
    _ ≤ (((L+1:ℕ):ℝ)⁻¹+η*t)/η := (le_div_iff₀ hη).mpr (by nlinarith [hx])
    _ = _ := by rw [add_div,mul_div_cancel_left₀ t (ne_of_gt hη)]

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl.singleton_regular_sat_oai := @OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl.singleton_regular_sat_oai
