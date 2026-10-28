-- Prove2me | solution 1 for OAI.DilutedSpinGlass.ReducedTopology.root_averaged_projectionShiftError_le_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:36:27.072041+00:00
-- url     : https://prove2.me/submissions/3211b807-4338-4b4a-aabf-50a24809e077

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

theorem covariance_centered (f g : Ω → ℝ) :
    P.covariance f g = P.expect (fun x => (f x - P.expect f) * (g x - P.expect g)) := by
  rw [covariance]
  calc
    _ = P.expect (fun x => f x * g x - f x * P.expect g -
        P.expect f * g x + P.expect f * P.expect g) := by simp
    _ = _ := P.expect_congr (fun x => by ring)

variable {n : ℕ}

/-- Elementary Jensen for the square, proved from its nonnegative variance. -/
theorem expect_sq_sub_expect (f : Ω → ℝ) :
    P.expect (fun x => (f x - P.expect f)^2) =
      P.expect (fun x => f x ^ 2) - P.expect f ^ 2 := by
  calc
    _ = P.expect (fun x => f x ^ 2 - 2 * P.expect f * f x + P.expect f ^ 2) :=
      P.expect_congr (fun _ => by ring)
    _ = _ := by simp; ring

theorem sq_expect_le_expect_sq (f : Ω → ℝ) :
    P.expect f ^ 2 ≤ P.expect (fun x => f x ^ 2) := by
  have h := P.expect_nonneg (fun x => sq_nonneg (f x - P.expect f))
  rw [expect_sq_sub_expect] at h
  linarith

/-- Jensen for the square root, including possible zero coordinates. -/
theorem expect_sqrt_le (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    P.expect (fun x => Real.sqrt (f x)) ≤ Real.sqrt (P.expect f) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [Real.sq_sqrt (hf _)] using
    P.sq_expect_le_expect_sq (fun x => Real.sqrt (f x))

/-- Total variance at one edge of a finite probability tree. -/
theorem variance_bind {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ)
    (f : Ω × Λ → ℝ) :
    (P.bind Q).covariance f f =
      P.expect (fun x => (Q x).covariance (fun y => f (x,y)) (fun y => f (x,y))) +
        P.covariance (fun x => (Q x).expect (fun y => f (x,y)))
          (fun x => (Q x).expect (fun y => f (x,y))) := by
  simp only [covariance, expect_bind, expect_sub]
  ring

theorem covariance_self_nonneg (f : Ω → ℝ) : 0 ≤ P.covariance f f := by
  rw [covariance_centered]
  exact P.expect_nonneg (fun x => mul_self_nonneg _)

/-- A bounded spin product has total conditional variance at most one. -/
theorem covariance_self_le_one {f : Ω → ℝ} (hf : ∀ x, |f x| ≤ 1) :
    P.covariance f f ≤ 1 := by
  have hs : P.expect (fun x => f x * f x) ≤ 1 := by
    rw [← P.expect_const 1]
    apply P.expect_mono
    intro x
    nlinarith [sq_le_sq.mpr (show |f x| ≤ |(1 : ℝ)| by simpa using hf x)]
  unfold covariance
  nlinarith [sq_nonneg (P.expect f)]


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

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProjection
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

lemma expect_comm {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (f : Ω → Λ → ℝ) :
    P.expect (fun x => Q.expect (f x)) = Q.expect (fun y => P.expect (fun x => f x y)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

/-- Product replacement on bounded spin coordinates, with its exact finite
sum of coordinate errors. -/
theorem bounded_product_difference {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i-g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hF := hf a (Finset.mem_insert_self a s)
    have hG : |∏ i ∈ s, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) hg'
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
    calc
      _ = |f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))+(f a-g a)*(∏ i ∈ s, g i)| := by
        congr 1; ring
      _ ≤ |f a| * |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)|+|f a-g a| * |∏ i ∈ s, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))) ((f a-g a)*(∏ i ∈ s, g i))
      _ ≤ 1*(∑ i ∈ s, |f i-g i|)+|f a-g a| * 1 :=
        add_le_add (mul_le_mul hF (ih hf' hg') (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hG (abs_nonneg _))
      _ = _ := by ring

theorem bounded_product_difference_sq {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    ((∏ i, f i)-(∏ i, g i))^2 ≤ (Fintype.card ι : ℝ)*∑ i, (f i-g i)^2 := by
  have hb := bounded_product_difference Finset.univ f g (fun i _ => hf i) (fun i _ => hg i)
  have hn : 0 ≤ ∑ i, |f i-g i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |f i-g i|)
  simp only [Finset.card_univ,sq_abs] at hs
  have hsq : ((∏ i, f i)-(∏ i, g i))^2 ≤ (∑ i, |f i-g i|)^2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hn] using hb)
  exact hsq.trans hs

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

/-- The one-vertex delay inequality decor:one-vertex-shift. The left side
compares independent child continuations with one shared extra transition. -/
theorem product_mean_shift_sq (P : FiniteLaw Ω) {ι : Type*} [Fintype ι]
    (f : ι → Ω → ℝ) (hf : ∀ i x, |f i x| ≤ 1) :
    ((∏ i, P.expect (f i))-P.expect (fun x => ∏ i, f i x))^2 ≤
      (Fintype.card ι : ℝ)*∑ i, P.covariance (f i) (f i) := by
  have hh := P.sq_expect_le_expect_sq (fun x => (∏ i, f i x)-(∏ i, P.expect (f i)))
  simp only [expect_sub,expect_const] at hh
  have hb := P.expect_mono (fun x => bounded_product_difference_sq
    (fun i => f i x) (fun i => P.expect (f i)) (fun i => hf i x)
    (fun i => P.abs_expect_le (hf i)))
  rw [expect_mul_left,expect_fintype_sum] at hb
  simp_rw [expect_sq_sub_expect] at hb
  simp only [covariance,pow_two] at hh hb ⊢
  nlinarith

end FiniteLaw
end DilutedSpinGlass

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem leafProduct_eq_prod {n : ℕ} (S : PrescribedTree n)
    (f : FinitePath Ω n → ℝ) (z : Sample Ω S) :
    leafProduct S f z = ∏ a : Leaf S, f (pathAt S a z) := by
  induction S with
  | leaf =>
    change f () = ∏ _ : Unit, f ()
    simp
  | @node n k C ih =>
    simp only [leafProduct]
    change _ = ∏ a : (i : Fin k) × Leaf (C i), f (pathAt (.node k C) a z)
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl (fun i _ => ih i (fun y => f ((z i).1,y)) (z i).2)

theorem treeMean_eq_expect {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (f : FinitePath Ω n → ℝ) : treeMean S T f = (sampleLaw S T).expect (leafProduct S f) := by
  induction S with
  | leaf =>
    change f () = KernelTower.unitLaw.expect (fun _ => f ())
    rw [FiniteLaw.expect_const]
  | @node n k C ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω n) at T
    rcases T with ⟨P,Q⟩
    change (Ω × FinitePath Ω n) → ℝ at f
    change (∏ i, P.expect (fun a => treeMean (C i) (Q a) (fun y => f (a,y)))) =
      (FiniteLaw.pi (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))).expect
        (fun z => ∏ i, leafProduct (C i) (fun y => f ((z i).1,y)) (z i).2)
    rw [FiniteLaw.expect_pi_product (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))
      (fun i (z : Ω × Sample Ω (C i)) => leafProduct (C i) (fun y => f (z.1,y)) z.2)]
    apply Finset.prod_congr rfl
    intro i _
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact ih i (Q a) (fun y => f (a,y))

omit [Fintype Ω] in
theorem leafProduct_bound {n : ℕ} (S : PrescribedTree n)
    {f : FinitePath Ω n → ℝ} (hf : ∀ x, |f x| ≤ 1) (z : Sample Ω S) :
    |leafProduct S f z| ≤ 1 := by
  rw [leafProduct_eq_prod,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun a _ => hf (pathAt S a z))

theorem treeMean_bound {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    {f : FinitePath Ω n → ℝ} (hf : ∀ x, |f x| ≤ 1) : |treeMean S T f| ≤ 1 := by
  rw [treeMean_eq_expect]
  exact (sampleLaw S T).abs_expect_le (leafProduct_bound S hf)

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Literal delay of a branching vertex. Every child loses one initial unary
transition; that transition is instead shared by all the children. Both terms
are expectations of the actual prescribed-tree products under the same tower. -/
theorem treeMean_one_vertex_shift {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n)
    (T : KernelTower Ω (n+2)) (f : FinitePath Ω (n+2) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    (treeMean (.node k (fun i => unary (C i))) T f-
      treeMean (unary (.node k C)) T f)^2 ≤
      (k : ℝ)*∑ i, T.1.covariance
        (fun a => treeMean (unary (C i)) (T.2 a) (fun y => f (a,y)))
        (fun a => treeMean (unary (C i)) (T.2 a) (fun y => f (a,y))) := by
  change FiniteLaw Ω × (Ω → KernelTower Ω (n+1)) at T
  rcases T with ⟨P,Q⟩
  change (Ω × FinitePath Ω (n+1)) → ℝ at f
  have h := P.product_mean_shift_sq
    (fun i a => treeMean (unary (C i)) (Q a) (fun y => f (a,y)))
    (fun i a => treeMean_bound (unary (C i)) (Q a) (fun y => hf (a,y)))
  simp only [Fintype.card_fin] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  change (∏ _ : Fin 1, P.expect (fun a => treeMean (.node k C) (Q a) (fun y => f (a,y)))) = _
  simp only [Fin.prod_univ_one]
  apply P.expect_congr
  intro a
  change (∏ i, (Q a).1.expect (fun b => treeMean (C i) ((Q a).2 b) (fun y => f (a,(b,y))))) = _
  simp only [treeMean_unary]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SplitDepthContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

lemma tailMean_bound (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x| ≤ 1) (x : FinitePath Ω (n+r)) :
    |tailMean S r T f x| ≤ 1 := by
  induction r with
  | zero => exact treeMean_bound S T hf
  | succ r ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

lemma tailMean_expect (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) :
    (KernelTower.law (n+r) T).expect (tailMean S r T f) = treeMean (stem S r) T f := by
  induction r with
  | zero => exact FiniteLaw.expect_const _ _
  | succ r ih =>
    have he := KernelTower.law_succ_expect (Ω := Ω) (n+r) T (tailMean S (r+1) T f)
    calc
      _ = _ := he
      _ = _ := by
        simp only [stem,treeMean_unary,tailMean]
        exact T.1.expect_congr (fun a => ih (T.2 a) (fun y => f (a,y)))

lemma tailVariance_nonneg (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) : 0 ≤ tailVariance S r T f :=
  FiniteLaw.covariance_self_nonneg _ _

lemma tailVariance_le_one (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x| ≤ 1) : tailVariance S r T f ≤ 1 :=
  FiniteLaw.covariance_self_le_one _ (tailMean_bound S r T f hf)

lemma tailVariance_step (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r+1))
    (f : FinitePath Ω (n+r+1) → ℝ) :
    tailVariance S (r+1) T f =
      T.1.covariance (fun a => treeMean (stem S r) (T.2 a) (fun y => f (a,y)))
        (fun a => treeMean (stem S r) (T.2 a) (fun y => f (a,y))) +
      T.1.expect (fun a => tailVariance S r (T.2 a) (fun y => f (a,y))) := by
  have h := T.1.variance_bind (fun a => KernelTower.law (n+r) (T.2 a)) (tailMean S (r+1) T f)
  change tailVariance S (r+1) T f = _ at h
  simp only [tailMean,tailMean_expect] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [add_comm]
  rfl

lemma splitShiftEnergy_step_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+2)) (f : FinitePath Ω (n+r+2) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    splitShiftEnergy k C (r+1) T f ≤
      (k:ℝ)*∑ i, T.1.covariance
        (fun a => treeMean (stem (C i) (r+1)) (T.2 a) (fun y => f (a,y)))
        (fun a => treeMean (stem (C i) (r+1)) (T.2 a) (fun y => f (a,y))) +
      T.1.expect (fun a => splitShiftEnergy k C r (T.2 a) (fun y => f (a,y))) := by
  unfold splitShiftEnergy
  rw [Fin.sum_univ_succ]
  have hi := treeMean_one_vertex_shift k (fun i => stem (C i) r) T f hf
  apply add_le_add
  · simp only [Fin.castSucc_zero,splitFamily_zero,splitFamily_succ,stem]
    convert hi using 1 <;> first | rfl
  · rw [FiniteLaw.expect_fintype_sum]
    apply Finset.sum_le_sum
    intro d _
    simp only [Fin.castSucc_succ,splitFamily_succ,treeMean_unary]
    have h := T.1.sq_expect_le_expect_sq (fun a =>
      treeMean (splitFamily k C r d.castSucc) (T.2 a) (fun y => f (a,y)) -
      treeMean (splitFamily k C r d.succ) (T.2 a) (fun y => f (a,y)))
    rwa [FiniteLaw.expect_sub] at h

 
theorem splitShiftEnergy_le_variance (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    splitShiftEnergy k C r T f ≤ (k:ℝ)*∑ i, tailVariance (C i) (r+1) T f := by
  induction r with
  | zero =>
    simp only [splitShiftEnergy,Finset.univ_eq_empty,Finset.sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => tailVariance_nonneg _ _ _ _))
  | succ r ih =>
    calc
      _ ≤ _ := splitShiftEnergy_step_le k C r T f hf
      _ ≤ (k:ℝ)*∑ i, T.1.covariance
          (fun a => treeMean (stem (C i) (r+1)) (T.2 a) (fun y => f (a,y)))
          (fun a => treeMean (stem (C i) (r+1)) (T.2 a) (fun y => f (a,y))) +
          T.1.expect (fun a => (k:ℝ)*∑ i, tailVariance (C i) (r+1) (T.2 a) (fun y => f (a,y))) :=
        add_le_add le_rfl (T.1.expect_mono (fun a => ih (T.2 a) (fun y => f (a,y))
          (fun y => hf (a,y))))
      _ = _ := by
        conv_rhs => arg 2; arg 2; ext i; rw [tailVariance_step (C i) (r+1)]
        rw [Finset.sum_add_distrib,FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum,mul_add]

theorem splitShiftEnergy_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : splitShiftEnergy k C r T f ≤ (k:ℝ)^2 := by
  refine (splitShiftEnergy_le_variance k C r T f hf).trans ?_
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => tailVariance_le_one (C i) (r+1) T f hf))
    (show (0:ℝ) ≤ k by positivity)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,pow_two] using h

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SizeSpinRoot
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
variable {Ω : Type} [Fintype Ω] {n : ℕ}

lemma stemIncrementSq_zero (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ) :
    stemIncrementSq S (r+1) T f 0=
      T.1.covariance (fun a => treeMean (stem S r) (T.2 a) (fun y => f (a,y)))
        (fun a => treeMean (stem S r) (T.2 a) (fun y => f (a,y))) := by
  unfold stemIncrementSq
  refine (KernelTower.law_succ_expect (Ω := Ω) (n+r) T _).trans ?_
  change T.1.expect (fun a => (KernelTower.law (n+r) (T.2 a)).expect (fun y =>
    (stemMeanAt S r 0 (T.2 a) (fun z => f (a,z)) y-
      treeMean (stem S (r+1)) T f)^2)) = _
  simp only [stemMeanAt_zero,FiniteLaw.expect_const,stem,treeMean_unary]
  rw [FiniteLaw.covariance_centered]
  apply FiniteLaw.expect_congr
  intro a
  simp only [pow_two]
  rfl

lemma stemIncrementSq_succ (S : PrescribedTree n) (r : ℕ) (d : Fin r)
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ) :
    stemIncrementSq S (r+1) T f d.succ=
      T.1.expect (fun a => stemIncrementSq S r (T.2 a) (fun y => f (a,y)) d) := by
  unfold stemIncrementSq
  refine (KernelTower.law_succ_expect (Ω := Ω) (n+r) T _).trans ?_
  simp only [Fin.castSucc_succ]
  rfl

/-- Exact orthogonality/telescoping identity for the literal conditional
means. Increments are compared on the same sampled prefix. -/
theorem sum_stemIncrementSq_eq (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) :
    (∑ d : Fin r, stemIncrementSq S r T f d)=tailVariance S r T f := by
  induction r with
  | zero => simp [tailVariance,tailMean,FiniteLaw.covariance]
  | succ r ih =>
    rw [Fin.sum_univ_succ,stemIncrementSq_zero,tailVariance_step]
    congr 1
    simp_rw [stemIncrementSq_succ]
    rw [← FiniteLaw.expect_fintype_sum]
    exact T.1.expect_congr (fun a => ih (T.2 a) (fun y => f (a,y)))

/-- Scalar decor:martingale-energy, with no kernel or population-size
constant and no assumed filtration theorem. -/
theorem sum_stemIncrementSq_le_one (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x|≤1) :
    (∑ d : Fin r, stemIncrementSq S r T f d) ≤ 1 := by
  rw [sum_stemIncrementSq_eq]
  exact tailVariance_le_one S r T f hf

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualPrefix
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

lemma bounded_product_one_difference_sq {ι : Type*} [Fintype ι]
    (F G : ι → ℝ) (a : ι) (hF : ∀ i, |F i| ≤ 1) (hG : ∀ i, |G i| ≤ 1)
    (he : ∀ i, i ≠ a → F i=G i) : ((∏ i, F i)-(∏ i, G i))^2 ≤ (F a-G a)^2 := by
  classical
  have hb := bounded_product_difference Finset.univ F G (fun i _ => hF i) (fun i _ => hG i)
  have hs : (∑ i, |F i-G i|) = |F a-G a| := by
    apply Finset.sum_eq_single a
    · intro b _ hba
      rw [he b hba, sub_self,abs_zero]
    · simp
  rw [hs] at hb
  exact sq_le_sq.mpr hb

namespace PrescribedTree
variable {Ω : Type} [Fintype Ω] {n : ℕ}

theorem treeMean_node_one_difference_sq (k : ℕ+) (C D : Fin k → PrescribedTree n)
    (i : Fin k) (he : ∀ j, j ≠ i → C j=D j) (T : KernelTower Ω (n+1))
    (f : FinitePath Ω (n+1) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (treeMean (.node k C) T f-treeMean (.node k D) T f)^2 ≤ T.1.expect (fun a =>
      (treeMean (C i) (T.2 a) (fun y => f (a,y))-treeMean (D i) (T.2 a) (fun y => f (a,y)))^2) := by
  have h := bounded_product_one_difference_sq
    (fun j => T.1.expect (fun a => treeMean (C j) (T.2 a) (fun y => f (a,y))))
    (fun j => T.1.expect (fun a => treeMean (D j) (T.2 a) (fun y => f (a,y)))) i
    (fun j => T.1.abs_expect_le (fun a => treeMean_bound (C j) (T.2 a) (fun y => hf (a,y))))
    (fun j => T.1.abs_expect_le (fun a => treeMean_bound (D j) (T.2 a) (fun y => hf (a,y))))
    (by intro j hj; rw [he j hj])
  apply h.trans
  have hh := T.1.sq_expect_le_expect_sq (fun a =>
    treeMean (C i) (T.2 a) (fun y => f (a,y))-treeMean (D i) (T.2 a) (fun y => f (a,y)))
  rwa [FiniteLaw.expect_sub] at hh

end PrescribedTree
end DilutedSpinGlass
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_SpinRootData
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
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

lemma uniform_equiv (e : Ω ≃ Ω) (F : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect (fun x => F (e x)) = (uniform : FiniteLaw Ω).expect F := by
  unfold expect uniform
  exact Equiv.sum_comp e (fun x => (Fintype.card Ω:ℝ)⁻¹*F x)

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.instDecidable_solutions
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {L : ℕ} [NeZero L]


lemma depthLaw_projection (e : β → α) (he : Function.Injective e)
    (τ : β → Equiv.Perm (Fin L)) (F : (β → Fin L) → ℝ) :
    (depthLaw α L).expect (fun q => F (coordinateProjection e τ q)) = (depthLaw β L).expect F := by
  unfold depthLaw coordinateProjection
  rw [FiniteLaw.expect_pi_injective (fun _ : α => (FiniteLaw.uniform : FiniteLaw (Fin L))) e he
    (fun q : β → Fin L => F (fun i => τ i (q i)))]
  have h := FiniteLaw.expect_pi_weighted_map
    (fun _ : β => (FiniteLaw.uniform : FiniteLaw (Fin L)))
    (fun _ : β => (FiniteLaw.uniform : FiniteLaw (Fin L)))
    (fun i => τ i) (fun _ _ => 1) (fun _ _ => 1)
    (fun i g => by simpa only [one_mul] using FiniteLaw.uniform_equiv (τ i) g) F
  simpa only [Finset.prod_const_one,mul_one] using h

/-- Exact fiber comparison with normalized unused coordinates. The retained
coordinates may independently be shifted by any permutation. -/
theorem fiber_bound (e : β → α) (he : Function.Injective e)
    (τ : β → Equiv.Perm (Fin L)) (D : (α → Fin L) → Prop) (E : (β → Fin L) → Prop)
    (hDE : ∀ q, D q → E (coordinateProjection e τ q)) (F : (β → Fin L) → ℝ)
    (hF : ∀ q, 0 ≤ F q) : average D (fun q => F (coordinateProjection e τ q)) ≤ average E F := by
  calc
    _ ≤ (depthLaw α L).expect (fun q =>
        if E (coordinateProjection e τ q) then F (coordinateProjection e τ q) else 0) := by
      apply FiniteLaw.expect_mono
      intro q
      by_cases hd : D q
      · rw [ite_eq_left hd,ite_eq_left (hDE q hd)]
      · rw [ite_eq_right hd]
        split_ifs
        · exact hF _
        · exact le_rfl
    _ = _ := depthLaw_projection e he τ (fun y => if E y then F y else 0)

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularDepth
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance regularDepthPropDecidable_r5a8952_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {L : ℕ} [NeZero L]

lemma rotate_val_of_room (q : Fin L) (hq : q.val+1 < L) :
    (finRotate L q).val=q.val+1 := by
  cases L with
  | zero => exact q.elim0
  | succ n =>
    rcases q with ⟨v,hv⟩
    change v+1<n+1 at hq
    have hn : v<n := by omega
    exact congrArg Fin.val (finRotate_of_lt hn)

omit [Fintype α] [DecidableEq α] in
lemma regular_room {η : ℝ} (hlarge : 1 < η*(L:ℝ)) {q : α → Fin L}
    (hq : Regular η q) (i : α) : (q i).val+1 < L := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hi := (div_lt_iff₀ hL).mp (hq.1 i).2
  have hh : ((q i).val:ℝ)+1 < (L:ℝ) := by nlinarith
  exact_mod_cast hh

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledTopology
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

namespace ReducedTopology

attribute [local instance] OAI.DilutedSpinGlass.instDecidable_solutions
lemma admissible_mono_lower (S : ReducedTopology) (q : S.Vertex → ℕ)
    {lo lo' hi : ℕ} (hlo : lo'≤lo) (h : Admissible S q lo hi) : Admissible S q lo' hi := by
  cases S with
  | leaf => trivial
  | node k hk C => exact ⟨hlo.trans h.1,h.2⟩

lemma admissible_lower (S : ReducedTopology) (q : S.Vertex → ℕ) {lo hi : ℕ}
    (h : Admissible S q lo hi) (v : S.Vertex) : lo ≤ q v := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none => exact h.1
    | some v => exact h.1.trans ((Nat.le_succ _).trans (ih v.1 _ (h.2.2 v.1) v.2))

lemma admissible_upper (S : ReducedTopology) (q : S.Vertex → ℕ) {lo hi : ℕ}
    (h : Admissible S q lo hi) (v : S.Vertex) : q v < hi := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none => exact h.2.1
    | some v => exact ih v.1 _ (h.2.2 v.1) v.2

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- Before its first scheduled branching, the realized topology is exactly
an initial unary stem; all later vertex assignments are unchanged. -/
lemma realize_stem (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d+r ≤ q v) :
    realize (n+r) d S q = PrescribedTree.stem (realize n (d+r) S q) r := by
  induction r generalizing d with
  | zero => rfl
  | succ r ih =>
    have hh : ∀ v, d+1+r ≤ q v := by intro v; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq v
    cases S with
    | leaf =>
      change PrescribedTree.unary (realize (n+r) (d+1) leaf q) =
        PrescribedTree.unary (PrescribedTree.stem (realize n (d+(r+1)) leaf q) r)
      congr 1
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (d+1) hh
    | node k hk C =>
      have hd : d<q none := by have := hq none; omega
      change realize (n+r+1) d (node k hk C) q = _
      rw [realize,ite_eq_left hd]
      change PrescribedTree.unary _ = PrescribedTree.unary _
      apply congrArg PrescribedTree.unary
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (d+1) hh

/-- The realized topology with one ranged root depth is the literal
split family, not just an isomorphic unordered or unlabeled tree. -/
theorem realize_splitFamily (k : ℕ+) (hk : 2 ≤ (k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : (i : Fin k) → (C i).Vertex → ℕ) (n r d : ℕ)
    (hQ : ∀ i v, d+r+1 ≤ Q i v) (t : Fin (r+1)) :
    realize (n+r+1) d (node k hk C) (rootSchedule (d+t.val) Q) =
      PrescribedTree.splitFamily k (fun i => realize n (d+r+1) (C i) (Q i)) r t := by
  induction r generalizing d with
  | zero =>
    have ht : t=0 := Fin.eq_zero t
    subst t
    simp only [Nat.add_zero,Fin.val_zero,realize,rootSchedule,lt_self_iff_false,
      ite_false,PrescribedTree.splitFamily]
  | succ r ih =>
    refine Fin.cases ?_ (fun t => ?_) t
    · rw [PrescribedTree.splitFamily_zero]
      simp only [Fin.val_zero,Nat.add_zero,realize,rootSchedule,lt_self_iff_false,
        ite_false]
      congr 1
      funext i
      have hh := realize_stem n (r+1) (d+1) (C i) (Q i) (by
        intro v
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hQ i v)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    · rw [PrescribedTree.splitFamily_succ]
      have hd : d<d+t.succ.val := by simp only [Fin.val_succ]; omega
      rw [realize]
      change (if d<d+t.succ.val then _ else _) = _
      rw [ite_eq_left hd]
      apply congrArg PrescribedTree.unary
      have hh := ih (d+1) (by
        intro i v
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hQ i v) t
      convert hh using 1 <;> (try simp only [Fin.val_succ,Nat.add_comm,Nat.add_left_comm]) <;> rfl

/-- Genuine one-coordinate energy bound for a scheduled reduced topology.
Every descendant depth is held fixed while the current branching depth is
ranged over the full available interval. All transition kernels are arbitrary. -/
theorem scheduled_split_energy_le (k : ℕ+) (hk : 2 ≤ (k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : (i : Fin k) → (C i).Vertex → ℕ) (n r d : ℕ)
    (hQ : ∀ i v, d+r+1 ≤ Q i v)
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    (∑ t : Fin r,
      (PrescribedTree.treeMean
        (realize (n+r+1) d (node k hk C) (rootSchedule (d+t.val) Q)) T f -
       PrescribedTree.treeMean
        (realize (n+r+1) d (node k hk C) (rootSchedule (d+t.val+1) Q)) T f)^2) ≤ (k:ℝ)^2 := by
  have h := PrescribedTree.splitShiftEnergy_le k
    (fun i => realize n (d+r+1) (C i) (Q i)) r T f hf
  unfold PrescribedTree.splitShiftEnergy at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro t _
  congr 2
  · exact congrArg (fun S => PrescribedTree.treeMean S T f)
      (realize_splitFamily k hk C Q n r d hQ t.castSucc)
  · have he := realize_splitFamily k hk C Q n r d hQ t.succ
    simpa only [Fin.val_succ,Nat.add_assoc] using congrArg (fun S => PrescribedTree.treeMean S T f) he

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_VertexContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators
namespace PrescribedTree
variable {Ω : Type} [Fintype Ω]

lemma node_family_energy_le {h : ℕ} {ι : Type*} [Fintype ι]
    (k : ℕ+) (U V : ι → Fin k → PrescribedTree h) (a : Fin k)
    (he : ∀ t j, j ≠ a → U t j=V t j) (B : ℝ)
    (hB : ∀ (T : KernelTower Ω h) (f : FinitePath Ω h → ℝ), (∀ x, |f x| ≤ 1) →
      (∑ t, (treeMean (U t a) T f-treeMean (V t a) T f)^2) ≤ B)
    (T : KernelTower Ω (h+1)) (f : FinitePath Ω (h+1) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t, (treeMean (.node k (U t)) T f-treeMean (.node k (V t)) T f)^2) ≤ B := by
  calc
    _ ≤ ∑ t, T.1.expect (fun x =>
        (treeMean (U t a) (T.2 x) (fun y => f (x,y))-
          treeMean (V t a) (T.2 x) (fun y => f (x,y)))^2) :=
      Finset.sum_le_sum (fun t _ => treeMean_node_one_difference_sq k (U t) (V t) a (he t) T f hf)
    _ = T.1.expect (fun x => ∑ t,
        (treeMean (U t a) (T.2 x) (fun y => f (x,y))-
          treeMean (V t a) (T.2 x) (fun y => f (x,y)))^2) :=
      (FiniteLaw.expect_fintype_sum _ _).symm
    _ ≤ T.1.expect (fun _ => B) := T.1.expect_mono (fun x => hB (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
    _ = B := FiniteLaw.expect_const _ _

lemma unary_family_energy_le {h : ℕ} {ι : Type*} [Fintype ι]
    (U V : ι → PrescribedTree h) (B : ℝ)
    (hB : ∀ (T : KernelTower Ω h) (f : FinitePath Ω h → ℝ), (∀ x, |f x| ≤ 1) →
      (∑ t, (treeMean (U t) T f-treeMean (V t) T f)^2) ≤ B)
    (T : KernelTower Ω (h+1)) (f : FinitePath Ω (h+1) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t, (treeMean (unary (U t)) T f-treeMean (unary (V t)) T f)^2) ≤ B := by
  exact node_family_energy_le 1 (fun t _ => U t) (fun t _ => V t) 0
    (by intro t j hj; exact False.elim (hj (Fin.eq_zero j))) B hB T f hf

end PrescribedTree

namespace ReducedTopology

attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.vertexContinuityDecidable
lemma update_root {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (q : (node k hk C).Vertex → ℕ) (t : ℕ) :
    updateCoordinate q none t = rootSchedule t (fun i v => q (some ⟨i,v⟩)) := by
  funext v
  cases v <;> simp [rootSchedule]

lemma update_desc_root {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (q : (node k hk C).Vertex → ℕ) (i : Fin k) (v : (C i).Vertex) (t : ℕ) :
    updateCoordinate q (some ⟨i,v⟩) t none = q none := by
  simp

lemma update_desc_same {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (q : (node k hk C).Vertex → ℕ) (i : Fin k) (v : (C i).Vertex) (t : ℕ) :
    (fun w => updateCoordinate q (some ⟨i,v⟩) t (some ⟨i,w⟩)) =
      updateCoordinate (fun w => q (some ⟨i,w⟩)) v t := by
  funext w
  by_cases hw : w=v
  · subst w; simp
  · have hn : (some ⟨i,w⟩ : (node k hk C).Vertex) ≠ some ⟨i,v⟩ := by
      intro hh
      have he := Option.some.inj hh
      exact hw (Sigma.mk.inj he).2.eq
    simp only [updateCoordinate_of_ne hw,updateCoordinate_of_ne hn]

lemma update_desc_other {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (q : (node k hk C).Vertex → ℕ) (i : Fin k) (v : (C i).Vertex) (t : ℕ)
    (j : Fin k) (hj : j ≠ i) :
    (fun w => updateCoordinate q (some ⟨i,v⟩) t (some ⟨j,w⟩)) = (fun w => q (some ⟨j,w⟩)) := by
  funext w
  apply updateCoordinate_of_ne
  intro hh
  exact hj (congrArg Sigma.fst (Option.some.inj hh))

/-- Root-coordinate case at the lesser endpoint, extracted from admissible
schedules alone. The descendant-depth gap is a consequence, not an analytic
hypothesis or a presumed continuity conclusion. -/
lemma root_vertex_energy_le {Ω : Type} [Fintype Ω]
    (H d r : ℕ) (k : ℕ+) (hk : 2 ≤ (k:ℕ)) (C : Fin k → ReducedTopology)
    (q : (node k hk C).Vertex → ℕ)
    (ha : ∀ t : Fin (r+1), Admissible (node k hk C) (updateCoordinate q none (d+t.val)) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t : Fin r,
      (PrescribedTree.treeMean (realize H d (node k hk C) (updateCoordinate q none (d+t.castSucc.val))) T f-
       PrescribedTree.treeMean (realize H d (node k hk C) (updateCoordinate q none (d+t.succ.val))) T f)^2) ≤ (k:ℝ)^2 := by
  have hr : r+1≤H := by
    have hh := (ha (Fin.last r)).2.1
    simp only [Fin.val_last] at hh
    simp only [updateCoordinate_self] at hh
    omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hr
  have hH : H=n+r+1 := by omega
  clear hn
  subst H
  have hQ : ∀ i v, d+r+1 ≤ q (some ⟨i,v⟩) := by
    intro i v
    have hh := (ha (Fin.last r)).2.2 i
    have hh' := admissible_lower (C i) _ hh v
    simpa [updateCoordinate] using hh'
  have he := scheduled_split_energy_le k hk C (fun i v => q (some ⟨i,v⟩)) n r d hQ T f hf
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro t _
  simp only [update_root (hk := hk),Fin.val_castSucc,Fin.val_succ,Nat.add_assoc]


/-- Squared one-grid-step changes at an arbitrary vertex of a scheduled
reduced topology. All other assigned depths are fixed; no ancestral context
or conditional-mean contraction is supplied as a hypothesis. -/
theorem scheduled_vertex_energy_le {Ω : Type} [Fintype Ω]
    (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (v : S.Vertex)
    (lo r : ℕ)
    (ha : ∀ t : Fin (r+1), Admissible S (updateCoordinate q v (lo+t.val)) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t : Fin r,
      (PrescribedTree.treeMean (realize H d S (updateCoordinate q v (lo+t.castSucc.val))) T f-
       PrescribedTree.treeMean (realize H d S (updateCoordinate q v (lo+t.succ.val))) T f)^2) ≤
      (vertexArity S v:ℝ)^2 := by
  induction H generalizing d S lo r with
  | zero =>
    have h := ha 0
    have hl := admissible_lower S _ h v
    have hu := admissible_upper S _ h v
    omega
  | succ H ih =>
    cases S with
    | leaf => exact v.elim
    | node k hk C =>
      cases v with
      | none =>
        have hd : d≤lo := by
          have h := (ha 0).1
          simpa using h
        by_cases he : d=lo
        · subst lo
          exact root_vertex_energy_le (H+1) d r k hk C q ha T f hf
        · have hlt : d<lo := by omega
          have hroot (t : Fin (r+1)) : d < updateCoordinate q none (lo+t.val) none := by
            simp only [updateCoordinate_self]
            omega
          have hu (t : Fin (r+1)) :
              realize (H+1) d (node k hk C) (updateCoordinate q none (lo+t.val)) =
              PrescribedTree.unary (realize H (d+1) (node k hk C) (updateCoordinate q none (lo+t.val))) := by
            rw [realize,ite_eq_left (hroot t)]
          simp_rw [hu]
          apply PrescribedTree.unary_family_energy_le _ _ _ ?_ T f hf
          intro T' f' hf'
          apply ih (d+1) (node k hk C) q none lo r ?_ T' f' hf'
          intro t
          exact ⟨hroot t,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (ha t).2⟩
      | some a =>
        obtain ⟨i,v⟩ := a
        have hd : d≤q none := by
          have h := (ha 0).1
          simpa only [update_desc_root (hk := hk)] using h
        by_cases he : d<q none
        · have hu (t : Fin (r+1)) :
              realize (H+1) d (node k hk C) (updateCoordinate q (some ⟨i,v⟩) (lo+t.val)) =
              PrescribedTree.unary (realize H (d+1) (node k hk C) (updateCoordinate q (some ⟨i,v⟩) (lo+t.val))) := by
            rw [realize,update_desc_root (hk := hk),ite_eq_left he]
          simp_rw [hu]
          apply PrescribedTree.unary_family_energy_le _ _ _ ?_ T f hf
          intro T' f' hf'
          apply ih (d+1) (node k hk C) q (some ⟨i,v⟩) lo r ?_ T' f' hf'
          intro t
          constructor
          · simpa only [update_desc_root (hk := hk)] using (Nat.succ_le_iff.mpr he)
          · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (ha t).2
        · have heq : q none=d := by omega
          have hu (t : Fin (r+1)) :
              realize (H+1) d (node k hk C) (updateCoordinate q (some ⟨i,v⟩) (lo+t.val)) =
              PrescribedTree.node k (fun j => realize H (d+1) (C j)
                (fun w => updateCoordinate q (some ⟨i,v⟩) (lo+t.val) (some ⟨j,w⟩))) := by
            rw [realize,update_desc_root (hk := hk),ite_eq_right he]
          simp_rw [hu]
          apply PrescribedTree.node_family_energy_le k _ _ i ?_ _ ?_ T f hf
          · intro t j hj
            rw [update_desc_other q i v _ j hj,update_desc_other q i v _ j hj]
          · intro T' f' hf'
            simp_rw [update_desc_same (hk := hk)]
            apply ih (d+1) (C i) (fun w => q (some ⟨i,w⟩)) v lo r ?_ T' f' hf'
            intro t
            have hh := (ha t).2.2 i
            simpa only [update_desc_root (hk := hk),update_desc_same (hk := hk),heq,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using hh

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_AdmissibleInterval
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

noncomputable local instance admissibleIntervalPropDecidable_r5a8952_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- With every other depth fixed, admissible values of one branching
coordinate form an interval. No spacing or regularity is needed here. -/
lemma admissible_update_between (S : ReducedTopology) (q : S.Vertex → ℕ) (v : S.Vertex)
    {a b t lo hi : ℕ} (hat : a≤t) (htb : t≤b)
    (ha : Admissible S (updateCoordinate q v a) lo hi)
    (hb : Admissible S (updateCoordinate q v b) lo hi) :
    Admissible S (updateCoordinate q v t) lo hi := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none =>
      simp only [update_root (hk := hk),Admissible,rootSchedule] at ha hb ⊢
      exact ⟨ha.1.trans hat,htb.trans_lt hb.2.1,
        fun i => admissible_mono_lower (C i) _ (Nat.succ_le_succ htb) (hb.2.2 i)⟩
    | some a =>
      obtain ⟨i,v⟩ := a
      constructor
      · simpa only [update_desc_root (hk := hk)] using ha.1
      constructor
      · simpa only [update_desc_root (hk := hk)] using ha.2.1
      intro j
      by_cases hj : j=i
      · subst j
        have haa := ha.2.2 i
        have hbb := hb.2.2 i
        simp only [update_desc_root (hk := hk),update_desc_same (hk := hk)] at haa hbb ⊢
        exact ih i _ v haa hbb
      · have haa := ha.2.2 j
        simpa only [update_desc_root (hk := hk),update_desc_other q i v _ j hj] using haa

/-- Interval form of the literal one-vertex Dirichlet-energy estimate. -/
theorem scheduled_vertex_Ico_energy_le {Ω : Type} [Fintype Ω]
    (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (v : S.Vertex)
    (a b : ℕ) (hab : a≤b)
    (ha : Admissible S (updateCoordinate q v a) d (d+H))
    (hb : Admissible S (updateCoordinate q v b) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t ∈ Finset.Ico a b,
      (PrescribedTree.treeMean (realize H d S (updateCoordinate q v t)) T f-
       PrescribedTree.treeMean (realize H d S (updateCoordinate q v (t+1))) T f)^2) ≤
      (vertexArity S v:ℝ)^2 := by
  have he := scheduled_vertex_energy_le H d S q v a (b-a) (by
    intro t
    apply admissible_update_between S q v (Nat.le_add_right _ _) ?_ ha hb
    have ht := t.isLt
    omega) T f hf
  let E : ℕ → ℝ := fun t =>
    (PrescribedTree.treeMean (realize H d S (updateCoordinate q v t)) T f-
     PrescribedTree.treeMean (realize H d S (updateCoordinate q v (t+1))) T f)^2
  have he' : (∑ t : Fin (b-a), E (a+t.val)) ≤ (vertexArity S v:ℝ)^2 := by
    simpa only [E,Fin.val_castSucc,Fin.val_succ,Nat.add_assoc] using he
  rw [Fin.sum_univ_eq_sum_range (fun t => E (a+t)) (b-a)] at he'
  change (∑ t ∈ Finset.Ico a b, E t) ≤ _
  rwa [Finset.sum_Ico_eq_sum_range]


/-- Restriction to ANY set of allowed one-step shifts cannot raise the
single-coordinate energy. The proof uses the actual admissible hull. -/
theorem scheduled_vertex_subset_energy_le {Ω : Type} [Fintype Ω]
    (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (v : S.Vertex)
    (I : Finset ℕ)
    (ha : ∀ t ∈ I, Admissible S (updateCoordinate q v t) d (d+H) ∧
      Admissible S (updateCoordinate q v (t+1)) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t ∈ I,
      (PrescribedTree.treeMean (realize H d S (updateCoordinate q v t)) T f-
       PrescribedTree.treeMean (realize H d S (updateCoordinate q v (t+1))) T f)^2) ≤
      (vertexArity S v:ℝ)^2 := by
  classical
  by_cases hI : I.Nonempty
  · have hm := I.min'_mem hI
    have hM := I.max'_mem hI
    have hsub : I ⊆ Finset.Ico (I.min' hI) (I.max' hI+1) := by
      intro t ht
      exact Finset.mem_Ico.mpr ⟨I.min'_le t ht,Nat.lt_succ_of_le (I.le_max' t ht)⟩
    calc
      _ ≤ ∑ t ∈ Finset.Ico (I.min' hI) (I.max' hI+1),
          (PrescribedTree.treeMean (realize H d S (updateCoordinate q v t)) T f-
           PrescribedTree.treeMean (realize H d S (updateCoordinate q v (t+1))) T f)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := scheduled_vertex_Ico_energy_le H d S q v _ _
        ((I.min'_le _ hM).trans (Nat.le_succ _)) (ha _ hm).1 (ha _ hM).2 T f hf
  · have he : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp only [he,Finset.sum_empty]
    positivity

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CoordinateFiber
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance instDecidable_solutions_1_r5a8952_1 (p : Prop) : Decidable p := Classical.propDecidable p
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma depthLaw_split (v : α) (F : (α → Fin L) → ℝ) :
    (depthLaw α L).expect F =
      (depthLaw {w : α // w ≠ v} L).expect (fun rest =>
        (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
          F ((Equiv.piSplitAt v (fun _ : α => Fin L)).symm (t,rest)))) := by
  unfold depthLaw
  rw [FiniteLaw.expect_pi_split _ v]
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  apply Finset.sum_congr rfl
  intro t _
  ring

 
theorem coordinate_fiber_bound (v : α) (F : (α → Fin L) → ℝ) (B : ℝ)
    (hF : ∀ rest : {w : α // w ≠ v} → Fin L,
      (∑ t : Fin L, F ((Equiv.piSplitAt v (fun _ : α => Fin L)).symm (t,rest))) ≤ B) :
    (depthLaw α L).expect F ≤ B/(L:ℝ) := by
  rw [depthLaw_split v F]
  calc
    _ ≤ (depthLaw {w : α // w ≠ v} L).expect (fun _ => B/(L:ℝ)) := by
      apply FiniteLaw.expect_mono
      intro rest
      unfold FiniteLaw.expect FiniteLaw.uniform
      simp only [Fintype.card_fin,← Finset.mul_sum]
      rw [mul_comm,← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (hF rest) (Nat.cast_nonneg _)
    _ = _ := FiniteLaw.expect_const _ _

end DilutedSpinGlass.DepthAverage

namespace DilutedSpinGlass

namespace DepthAverage
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

omit [Fintype α] in
lemma splitAt_values_update (v : α) (rest : {w : α // w ≠ v} → Fin L) (t : Fin L) :
    (fun w => ((Equiv.piSplitAt v (fun _ : α => Fin L)).symm (t,rest) w).val) =
      updateCoordinate
        (fun w => ((Equiv.piSplitAt v (fun _ : α => Fin L)).symm (0,rest) w).val) v t.val := by
  classical
  funext w
  by_cases h : w=v
  · subst w
    simp only [Equiv.piSplitAt_symm_apply,dite_true,updateCoordinate_self]
  · simp only [Equiv.piSplitAt_symm_apply,dite_eq_right h,updateCoordinate_of_ne h]

end DepthAverage
namespace ReducedTopology
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.instDecidable
variable {Ω : Type} [Fintype Ω] {L : ℕ} [NeZero L]

omit [NeZero L] in
lemma vertexChangeSq_nonneg (H d : ℕ) (S : ReducedTopology) (v : S.Vertex)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (q : S.Vertex → Fin L) :
    0 ≤ vertexChangeSq H d S v T f q := sq_nonneg _

 
theorem averaged_vertexChangeSq_le (H d : ℕ) (S : ReducedTopology) (v : S.Vertex)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun w => (q w).val) d (d+H) ∧
      Admissible S (updateCoordinate (fun w => (q w).val) v ((q v).val+1)) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    DepthAverage.average D (vertexChangeSq H d S v T f) ≤ (vertexArity S v:ℝ)^2/(L:ℝ) := by
  classical
  apply DepthAverage.coordinate_fiber_bound v
  intro rest
  let split (t : Fin L) : S.Vertex → Fin L :=
    (Equiv.piSplitAt v (fun _ : S.Vertex => Fin L)).symm (t,rest)
  let q0 : S.Vertex → ℕ := fun w => (split 0 w).val
  let E : ℕ → ℝ := fun t =>
    (PrescribedTree.treeMean (realize H d S (updateCoordinate q0 v t)) T f-
     PrescribedTree.treeMean (realize H d S (updateCoordinate q0 v (t+1))) T f)^2
  have hv (t : Fin L) : (split t v).val=t.val := by
    simp only [split,Equiv.piSplitAt_symm_apply,dite_true]
  have he (t : Fin L) : vertexChangeSq H d S v T f (split t)=E t.val := by
    unfold vertexChangeSq
    rw [DepthAverage.splitAt_values_update,updateCoordinate_update]
    rw [hv]
  let U : Finset (Fin L) := Finset.univ.filter (fun t => D (split t))
  let I : Finset ℕ := U.image Fin.val
  have hadm : ∀ t ∈ I, Admissible S (updateCoordinate q0 v t) d (d+H) ∧
      Admissible S (updateCoordinate q0 v (t+1)) d (d+H) := by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
    have hh := hD (split a) (Finset.mem_filter.mp ha).2
    rw [DepthAverage.splitAt_values_update,updateCoordinate_update,hv] at hh
    exact hh
  have hE := scheduled_vertex_subset_energy_le H d S q0 v I hadm T f hf
  change (∑ t : Fin L, if D (split t) then vertexChangeSq H d S v T f (split t) else 0) ≤ _
  simp_rw [he]
  rw [← Finset.sum_filter]
  have hs : (∑ t ∈ U, E t.val) = ∑ t ∈ I, E t := by
    symm
    exact Finset.sum_image (fun a _ b _ h => Fin.ext h)
  change (∑ t ∈ U, E t.val) ≤ _
  rw [hs]
  exact hE

end ReducedTopology
end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {N : ℕ}

lemma spatialSq_nonneg (x : Fin N → ℝ) : 0 ≤ spatialSq x :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularScheduleShift
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

noncomputable local instance regularScheduleShiftPropDecidable_r5a8952_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- An order-preserving re-assignment of every actual branching vertex
preserves the strict ancestral schedule. -/
lemma admissible_order_map (S : ReducedTopology) (q q' : S.Vertex → ℕ)
    {lo lo' hi hi' : ℕ} (hq : Admissible S q lo hi)
    (hl : ∀ v, lo' ≤ q' v) (hu : ∀ v, q' v < hi')
    (ho : ∀ u v, q u < q v → q' u < q' v) : Admissible S q' lo' hi' := by
  induction S generalizing lo lo' hi hi' with
  | leaf => trivial
  | node k hk C ih =>
    refine ⟨hl none,hu none,?_⟩
    intro i
    apply ih i (fun v => q (some ⟨i,v⟩)) (fun v => q' (some ⟨i,v⟩)) (hq.2.2 i)
    · intro v
      have hv := admissible_lower (C i) (fun v => q (some ⟨i,v⟩)) (hq.2.2 i) v
      exact ho none (some ⟨i,v⟩) hv
    · intro v; exact hu _
    · intro u v huv; exact ho _ _ huv

variable {L : ℕ} [NeZero L]

lemma regular_depth_gap {α : Type} {η : ℝ} (hlarge : 1<η*(L:ℝ))
    {q : α → Fin L} (hr : DepthAverage.Regular η q) (u v : α)
    (huv : (q u).val < (q v).val) : (q u).val+1 < (q v).val := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hne : u ≠ v := by intro h; subst v; omega
  have hh := hr.2 u v hne
  have hd : DepthAverage.normalized (q u) ≤ DepthAverage.normalized (q v) :=
    div_le_div_of_nonneg_right (by exact_mod_cast huv.le) hL.le
  rw [abs_of_nonpos (sub_nonpos.mpr hd)] at hh
  have hcast : ((q u).val:ℝ)+1 < ((q v).val:ℝ) := by
    unfold DepthAverage.normalized at hh
    have hh' : η*(L:ℝ) < ((q v).val:ℝ)-((q u).val:ℝ) := by
      apply (lt_div_iff₀ hL).mp
      rw [sub_div]
      linarith [hh]
    linarith
  exact_mod_cast hcast

lemma shifted_val_bounds {α : Type} {η : ℝ} (hlarge : 1<η*(L:ℝ))
    {q : α → Fin L} (hr : DepthAverage.Regular η q) (s : α → Bool) (v : α) :
    (q v).val ≤ (DepthAverage.shiftPerm (s v) (q v)).val ∧
    (DepthAverage.shiftPerm (s v) (q v)).val ≤ (q v).val+1 := by
  have hrm := DepthAverage.regular_room hlarge hr v
  cases hs : s v with
  | false =>
    simp only [DepthAverage.shiftPerm,Bool.false_eq_true,ite_false,Equiv.refl_apply]
    omega
  | true =>
    simp only [DepthAverage.shiftPerm,ite_true,DepthAverage.rotate_val_of_room _ hrm]
    omega

/-- All intermediate positive one-step shifts of a regular admissible
assignment are genuine admissible shapes, with the original horizon. -/
theorem admissible_regular_shift (S : ReducedTopology) {η : ℝ}
    (hlarge : 1<η*(L:ℝ)) (q : S.Vertex → Fin L)
    {lo : ℕ} (hq : Admissible S (fun v => (q v).val) lo L) (hr : DepthAverage.Regular η q)
    (s : S.Vertex → Bool) :
    Admissible S (fun v => (DepthAverage.shiftPerm (s v) (q v)).val) lo L := by
  apply admissible_order_map S (fun v => (q v).val) _ hq
  · intro v
    exact (admissible_lower S _ hq v).trans (shifted_val_bounds hlarge hr s v).1
  · intro v; exact (DepthAverage.shiftPerm (s v) (q v)).isLt
  · intro u v huv
    have hg := regular_depth_gap hlarge hr u v huv
    have hb := shifted_val_bounds hlarge hr s u
    have hc := shifted_val_bounds hlarge hr s v
    omega

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SimultaneousShift
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.simultaneousShiftPropDecidable
lemma real_telescope_sq_le (F : ℕ → ℝ) (n : ℕ) :
    (F 0-F n)^2 ≤ (n:ℝ)*∑ i : Fin n, (F i.val-F (i.val+1))^2 := by
  have h := @sq_sum_le_card_mul_sum_sq ℕ ℝ _ _ _ _ (Finset.range n)
    (fun i => F i-F (i+1))
  rw [Finset.sum_range_sub',Finset.card_range] at h
  rw [Fin.sum_univ_eq_sum_range (fun i => (F i-F (i+1))^2) n]
  exact h

namespace DepthAverage
attribute [local instance] OAI.DilutedSpinGlass.simultaneousShiftPropDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

omit [DecidableEq α] [NeZero L] in
lemma shiftPath_zero (s : α → Bool) (q : α → Fin L) : shiftPath s 0 q=q := by
  funext v
  simp only [shiftPath,coordinateProjection,id_eq,shiftPathFlag,Nat.not_lt_zero,ite_false,
    shiftPerm,Bool.false_eq_true,Equiv.refl_apply]

omit [DecidableEq α] [NeZero L] in
lemma shiftPath_full (s : α → Bool) (q : α → Fin L) :
    shiftPath s (Fintype.card α) q=coordinateProjection id (fun v => shiftPerm (s v)) q := by
  funext v
  simp only [shiftPath,coordinateProjection,id_eq,shiftPathFlag,
    (Fintype.equivFin α v).isLt,ite_true]

omit [DecidableEq α] [NeZero L] in
lemma shiftPath_step_false (s : α → Bool) (q : α → Fin L) (i : Fin (Fintype.card α))
    (hs : s ((Fintype.equivFin α).symm i)=false) :
    shiftPath s (i.val+1) q=shiftPath s i.val q := by
  funext v
  by_cases hvi : Fintype.equivFin α v=i
  · have hv : v=(Fintype.equivFin α).symm i := (Equiv.eq_symm_apply _).mpr hvi
    subst v
    simp only [shiftPath,coordinateProjection,shiftPathFlag,Equiv.apply_symm_apply,
      Nat.lt_succ_self,ite_true,lt_self_iff_false,ite_false,id_eq,hs]
  · have hvn : (Fintype.equivFin α v).val ≠ i.val := by intro h; exact hvi (Fin.ext h)
    have he : ((Fintype.equivFin α v).val < i.val+1) ↔
        ((Fintype.equivFin α v).val < i.val) := by omega
    simp only [shiftPath,coordinateProjection,shiftPathFlag,he]

lemma shiftPath_step_values {η : ℝ} (hlarge : 1<η*(L:ℝ))
    (s : α → Bool) (q : α → Fin L) (hr : Regular η q) (i : Fin (Fintype.card α))
    (hs : s ((Fintype.equivFin α).symm i)=true) :
    (fun v => (shiftPath s (i.val+1) q v).val)=
      updateCoordinate (fun v => (shiftPath s i.val q v).val)
        ((Fintype.equivFin α).symm i) ((shiftPath s i.val q ((Fintype.equivFin α).symm i)).val+1) := by
  funext v
  by_cases hv : v=(Fintype.equivFin α).symm i
  · subst v
    rw [updateCoordinate_self]
    simp only [shiftPath,coordinateProjection,shiftPathFlag,Equiv.apply_symm_apply,
      Nat.lt_succ_self,ite_true,lt_self_iff_false,ite_false,id_eq,hs,
      shiftPerm,Bool.false_eq_true,Equiv.refl_apply]
    exact rotate_val_of_room _ (regular_room hlarge hr _)
  · rw [updateCoordinate_of_ne hv]
    have hvn : (Fintype.equivFin α v).val ≠ i.val := by
      intro h
      exact hv ((Equiv.eq_symm_apply _).mpr (Fin.ext h))
    have he : ((Fintype.equivFin α v).val < i.val+1) ↔
        ((Fintype.equivFin α v).val < i.val) := by omega
    simp only [shiftPath,coordinateProjection,shiftPathFlag,he]

end DepthAverage
namespace ReducedTopology
attribute [local instance] OAI.DilutedSpinGlass.simultaneousShiftPropDecidable
variable {Ω : Type} [Fintype Ω] {L : ℕ} [NeZero L]

 
theorem averaged_simultaneous_shift_le (H d : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ)
    (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x|≤1) :
    DepthAverage.average D (fun q =>
      (PrescribedTree.treeMean (realize H d S (fun v => (q v).val)) T f-
       PrescribedTree.treeMean (realize H d S
         (fun v => (DepthAverage.shiftPerm (s v) (q v)).val)) T f)^2) ≤
      (Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) := by
  classical
  let b := Fintype.card S.Vertex
  let idx : Fin b → S.Vertex := (Fintype.equivFin S.Vertex).symm
  let G : ℕ → (S.Vertex → Fin L) → ℝ := fun t q =>
    PrescribedTree.treeMean (realize H d S (fun v => (DepthAverage.shiftPath s t q v).val)) T f
  have hg0 (q) : G 0 q=PrescribedTree.treeMean (realize H d S (fun v => (q v).val)) T f := by
    simp only [G,DepthAverage.shiftPath_zero]
  have hgb (q) : G b q=PrescribedTree.treeMean (realize H d S
        (fun v => (DepthAverage.shiftPerm (s v) (q v)).val)) T f := by
    simp only [G,b,DepthAverage.shiftPath_full,DepthAverage.coordinateProjection,id_eq]
  have ha (q) (hq : D q) (t : ℕ) :
      Admissible S (fun v => (DepthAverage.shiftPath s t q v).val) d L :=
    admissible_regular_shift S hlarge q (hD q hq).1 (hD q hq).2
      (DepthAverage.shiftPathFlag s t)
  have hstep (i : Fin b) : DepthAverage.average D (fun q => (G i.val q-G (i.val+1) q)^2) ≤
      (vertexArity S (idx i):ℝ)^2/(L:ℝ) := by
    by_cases hs : s (idx i)=false
    · have he (q) : G (i.val+1) q=G i.val q := by
        simp only [G,DepthAverage.shiftPath_step_false s q i hs]
      simp only [he,sub_self,zero_pow (by decide : 2≠0),DepthAverage.average,ite_self,
        FiniteLaw.expect_const]
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    · have hs' : s (idx i)=true := Bool.eq_true_of_not_eq_false hs
      let E : (S.Vertex → Fin L) → Prop := fun q =>
        Admissible S (fun v => (q v).val) d L ∧
        Admissible S (updateCoordinate (fun v => (q v).val) (idx i) ((q (idx i)).val+1)) d L
      have hm (q) (hq : D q) : E (DepthAverage.shiftPath s i.val q) := by
        constructor
        · exact ha q hq i.val
        · rw [← DepthAverage.shiftPath_step_values hlarge s q (hD q hq).2 i hs']
          exact ha q hq (i.val+1)
      have he (q) (hq : D q) : (G i.val q-G (i.val+1) q)^2=
          vertexChangeSq H d S (idx i) T f (DepthAverage.shiftPath s i.val q) := by
        unfold G vertexChangeSq
        rw [DepthAverage.shiftPath_step_values hlarge s q (hD q hq).2 i hs']
      have he' : DepthAverage.average D (fun q => (G i.val q-G (i.val+1) q)^2)=
          DepthAverage.average D (fun q => vertexChangeSq H d S (idx i) T f
            (DepthAverage.shiftPath s i.val q)) := by
        apply FiniteLaw.expect_congr
        intro q
        split_ifs with hq
        · exact he q hq
        · rfl
      rw [he']
      exact (DepthAverage.fiber_bound id Function.injective_id
        (fun v => DepthAverage.shiftPerm (DepthAverage.shiftPathFlag s i.val v)) D E hm
        (vertexChangeSq H d S (idx i) T f) (vertexChangeSq_nonneg H d S (idx i) T f)).trans
        (averaged_vertexChangeSq_le H d S (idx i) E (by simpa only [hheight] using
          (fun q (hq : E q) => hq)) T f hf)
  have hp (q) : (if D q then (G 0 q-G b q)^2 else 0) ≤
      (b:ℝ)*∑ i : Fin b, if D q then (G i.val q-G (i.val+1) q)^2 else 0 := by
    split_ifs with hq
    · exact real_telescope_sq_le (fun t => G t q) b
    · simp
  have hh := (DepthAverage.depthLaw S.Vertex L).expect_mono hp
  rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep i)
  have hind : (∑ i : Fin b, (vertexArity S (idx i):ℝ)^2)=
      ∑ v : S.Vertex, (vertexArity S v:ℝ)^2 :=
    by
      simpa only [idx,b] using Equiv.sum_comp (Fintype.equivFin S.Vertex).symm
        (fun v : S.Vertex => (vertexArity S v:ℝ)^2)
  rw [← Finset.sum_div,hind] at hsum
  have hb : (0:ℝ)≤b := Nat.cast_nonneg _
  have hfin := hh.trans (mul_le_mul_of_nonneg_left hsum hb)
  simpa only [DepthAverage.average,b,hg0,hgb,← mul_div_assoc] using hfin

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SpatialScheduledContinuity
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.spatialScheduledContinuityDepthDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_div (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) (c : ℝ) :
    average D (fun q => F q/c)=average D F/c := by
  unfold average
  rw [← FiniteLaw.expect_div]
  apply FiniteLaw.expect_congr
  intro q
  split_ifs <;> simp

lemma average_sum {ι : Type*} [Fintype ι] (D : (α → Fin L) → Prop)
    (F : ι → (α → Fin L) → ℝ) :
    average D (fun q => ∑ i, F i q)=∑ i, average D (F i) := by
  unfold average
  rw [← FiniteLaw.expect_fintype_sum]
  apply FiniteLaw.expect_congr
  intro q
  split_ifs <;> simp

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.spatialScheduledContinuityReducedDecidable
variable {Ω : Type} [Fintype Ω] {L N : ℕ} [NeZero L]

/-- Full vector-valued branching-depth part of decor:depth-continuity.
The constant b*sum(arity²) is independent of N, all transition kernels and
the spin function. N=0 obeys the same inequality without an extra hypothesis. -/
theorem averaged_spatialScheduleChange_le (H d : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (spatialScheduleChange H d S s T f) ≤
      (Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) := by
  classical
  unfold spatialScheduleChange
  rw [DepthAverage.average_div,DepthAverage.average_sum]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    averaged_simultaneous_shift_le H d hheight S η hlarge s D hD T (fun x => f x i) (fun x => hf x i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  by_cases hN : N=0
  · subst N
    simp only [Nat.cast_zero,div_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (Nat.cast_nonneg _)
  · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
    nlinarith [hh]

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProductEvaluationContinuity
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
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma stemMeanAt_bound (S : PrescribedTree n) (r : ℕ) (d : Fin (r+1))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ)
    (hf : ∀ x, |f x|≤1) (x : FinitePath Ω (n+r)) :
    |stemMeanAt S r d T f x|≤1 := by
  induction r with
  | zero => exact treeMean_bound S T hf
  | succ r ih =>
    refine Fin.cases ?_ (fun e => ?_) d
    · exact treeMean_bound (stem S (r+1)) T hf
    · exact ih e (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

lemma productStemIncrementSq_nonneg {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (d : Fin r) :
    0≤productStemIncrementSq C r T f d :=
  FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _)

lemma productStemIncrementSq_le {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x|≤1) (d : Fin r) :
    productStemIncrementSq C r T f d ≤
      (Fintype.card ι:ℝ)*∑ i, stemIncrementSq (C i) r T f d := by
  have h := (KernelTower.law (n+r) T).expect_mono (fun x =>
    bounded_product_difference_sq
      (fun i => stemMeanAt (C i) r d.succ T f x)
      (fun i => stemMeanAt (C i) r d.castSucc T f x)
      (fun i => stemMeanAt_bound (C i) r _ T f hf x)
      (fun i => stemMeanAt_bound (C i) r _ T f hf x))
  simpa only [productStemIncrementSq,stemIncrementSq,FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] using h

/-- Finite product martingale-energy bound. Only the number of proper
children occurs in the constant, not the depth, dimension or kernels. -/
theorem sum_productStemIncrementSq_le {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x|≤1) :
    (∑ d : Fin r, productStemIncrementSq C r T f d) ≤ (Fintype.card ι:ℝ)^2 := by
  calc
    _ ≤ ∑ d : Fin r, (Fintype.card ι:ℝ)*∑ i, stemIncrementSq (C i) r T f d :=
      Finset.sum_le_sum (fun d _ => productStemIncrementSq_le C r T f hf d)
    _ = (Fintype.card ι:ℝ)*∑ i, ∑ d : Fin r, stemIncrementSq (C i) r T f d := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (Fintype.card ι:ℝ)*∑ i : ι, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        sum_stemIncrementSq_le_one (C i) r T f hf)) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two]

/-- The evaluation-depth component of the manuscript's h_N error, with its
literal 1/L normalization and spatial average. Zero spatial size is included. -/
theorem averaged_productStemIncrement_spatial_le {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r L : ℕ) (U : Finset (Fin r))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ)
    (hf : ∀ x j, |f x j|≤1) :
    ((∑ d ∈ U, (∑ j : Fin N, productStemIncrementSq C r T (fun x => f x j) d)/(N:ℝ))/(L:ℝ)) ≤
      (Fintype.card ι:ℝ)^2/(L:ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  by_cases hN : N=0
  · subst N
    simp only [Nat.cast_zero,div_zero,Finset.sum_const_zero]
    positivity
  · rw [← Finset.sum_div,Finset.sum_comm]
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
    calc
      _ ≤ ∑ j : Fin N, (Fintype.card ι:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro j _
        exact (Finset.sum_le_univ_sum_of_nonneg (productStemIncrementSq_nonneg C r T (fun x => f x j))).trans
          (sum_productStemIncrementSq_le C r T (fun x => f x j) (fun x => hf x j))
      _ = _ := by simp [mul_comm]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TargetEvaluationContinuity
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

lemma productStemMeanAt_spatial_increment {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (d : Fin r) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → Fin N → ℝ) :
    (KernelTower.law (n+r) T).expect (fun x => FiniteLaw.spatialSq (fun i =>
      productStemMeanAt C r d.succ T f x i-productStemMeanAt C r d.castSucc T f x i))=
      (∑ j : Fin N, productStemIncrementSq C r T (fun x => f x j) d)/(N:ℝ) := by
  simp only [FiniteLaw.spatialSq,FiniteLaw.expect_div,FiniteLaw.expect_fintype_sum,
    productStemMeanAt,productStemIncrementSq]


end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TargetScheduleContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.targetScheduleAverageDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_expect {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (D : (α → Fin L) → Prop) (F : (α → Fin L) → Ω → ℝ) :
    average D (fun q => P.expect (F q))=P.expect (fun x => average D (fun q => F q x)) := by
  unfold average
  calc
    _ = (depthLaw α L).expect (fun q => P.expect (fun x => if D q then F q x else 0)) := by
      apply FiniteLaw.expect_congr
      intro q
      split_ifs with h
      · rfl
      · exact (P.expect_const 0).symm
    _ = _ := FiniteLaw.expect_comm _ _ _

lemma average_mono_on (D : (α → Fin L) → Prop) (F G : (α → Fin L) → ℝ)
    (h : ∀ q, D q → F q ≤ G q) : average D F ≤ average D G := by
  apply FiniteLaw.expect_mono
  intro q
  split_ifs with hq
  · exact h q hq
  · exact le_rfl

lemma average_mul_left (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) (c : ℝ) :
    average D (fun q => c*F q)=c*average D F := by
  unfold average
  rw [← FiniteLaw.expect_mul_left]
  apply FiniteLaw.expect_congr
  intro q
  split_ifs <;> simp

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.targetScheduleTopologyDecidable
variable {Ω : Type} [Fintype Ω] {L N : ℕ} [NeZero L]

omit [NeZero L] in
lemma scheduledTailProjection_bound (H d p : ℕ) (S : ReducedTopology)
    (q : S.Vertex → Fin L) (T : KernelTower Ω (H+p))
    (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (x : FinitePath Ω (H+p)) (i : Fin N) : |scheduledTailProjection H d p S q T f x i|≤1 :=
  PrescribedTree.tailMean_bound _ p T _ (fun y => hf y i) x

omit [NeZero L] in
lemma tailScheduleChange_succ (H d p : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω (H+(p+1))) (f : FinitePath Ω (H+(p+1)) → Fin N → ℝ) (q : S.Vertex → Fin L) :
    tailScheduleChange H d (p+1) S s T f q=
      T.1.expect (fun x => tailScheduleChange H d p S s (T.2 x) (fun y => f (x,y)) q) := by
  unfold tailScheduleChange
  exact KernelTower.law_succ_expect (Ω := Ω) (H+p) T _

/-- Uniform simultaneous schedule continuity after an arbitrary real sampled
prefix. In particular p=d gives the physical evaluation-depth geometry. -/
theorem averaged_tailScheduleChange_le (H d p : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (tailScheduleChange H d p S s T f) ≤
      (Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) := by
  induction p with
  | zero =>
    have he : tailScheduleChange (L := L) H d 0 S s T f=spatialScheduleChange H d S s T f := by
      funext q
      unfold tailScheduleChange scheduledTailProjection
      simp only [PrescribedTree.tailMean,FiniteLaw.expect_const,FiniteLaw.spatialSq,spatialScheduleChange]
      rfl
    rw [he]
    exact averaged_spatialScheduleChange_le H d hheight S η hlarge s D hD T f hf
  | succ p ih =>
    have he : tailScheduleChange (L := L) H d (p+1) S s T f=
        fun q => T.1.expect (fun x => tailScheduleChange H d p S s (T.2 x) (fun y => f (x,y)) q) :=
      funext (tailScheduleChange_succ H d p S s T f)
    rw [he,DepthAverage.average_expect]
    calc
      _ ≤ T.1.expect (fun _ => (Fintype.card S.Vertex:ℝ)*
          (∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ)) :=
        T.1.expect_mono (fun x => ih (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
      _ = _ := T.1.expect_const _

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProperChildScheduleContinuity
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- Bounded products are Lipschitz in the actual normalized spatial norm,
including the empty spatial dimension convention. -/
lemma spatialSq_product_difference_le (X Y : ι → Fin N → ℝ)
    (hX : ∀ j i, |X j i|≤1) (hY : ∀ j i, |Y j i|≤1) :
    spatialSq (fun i => (∏ j, X j i)-(∏ j, Y j i)) ≤
      (Fintype.card ι:ℝ)*∑ j, spatialSq (fun i => X j i-Y j i) := by
  unfold spatialSq
  calc
    _ ≤ (∑ i, (Fintype.card ι:ℝ)*∑ j, (X j i-Y j i)^2)/(N:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ =>
        bounded_product_difference_sq (fun j => X j i) (fun j => Y j i)
          (fun j => hX j i) (fun j => hY j i))) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      rw [mul_div_assoc,Finset.sum_div]

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.properChildSchedulePropDecidable
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]

omit [NeZero L] in
lemma tailScheduleChange_nonneg (H d p : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (q : S.Vertex → Fin L) :
    0≤tailScheduleChange H d p S s T f q :=
  FiniteLaw.expect_nonneg _ (fun _ => FiniteLaw.spatialSq_nonneg _)


theorem averaged_childScheduleProjection_change_le (H d p : ℕ) (hheight : d+H=L)
    (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (he : ∀ j, Function.Injective (e j))
    (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : (j : ι) → (C j).Vertex → Bool)
    (D : (α → Fin L) → Prop)
    (hD : ∀ q, D q → ∀ j, Admissible (C j) (fun v => (τ j v (q (e j v))).val) d L ∧
      DepthAverage.Regular η (DepthAverage.coordinateProjection (e j) (τ j) q))
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun q => (KernelTower.law (H+p) T).expect (fun x =>
      FiniteLaw.spatialSq (fun i => childScheduleProjection H d p C e τ (fun _ _ => false) T f q x i-
        childScheduleProjection H d p C e τ s T f q x i))) ≤
      (Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ) := by
  have hp (q : α → Fin L) : (KernelTower.law (H+p) T).expect (fun x =>
      FiniteLaw.spatialSq (fun i => childScheduleProjection H d p C e τ (fun _ _ => false) T f q x i-
        childScheduleProjection H d p C e τ s T f q x i)) ≤
        (Fintype.card ι:ℝ)*∑ j, tailScheduleChange H d p (C j) (s j) T f
          (DepthAverage.coordinateProjection (e j) (τ j) q) := by
    have hh := (KernelTower.law (H+p) T).expect_mono (fun x =>
      FiniteLaw.spatialSq_product_difference_le
        (fun j => scheduledTailProjection H d p (C j) (fun v => τ j v (q (e j v))) T f x)
        (fun j => scheduledTailProjection H d p (C j) (fun v => DepthAverage.shiftPerm (s j v) (τ j v (q (e j v)))) T f x)
        (fun j => scheduledTailProjection_bound H d p (C j) _ T f hf x)
        (fun j => scheduledTailProjection_bound H d p (C j) _ T f hf x))
    rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at hh
    exact hh
  calc
    _ ≤ DepthAverage.average D (fun q => (Fintype.card ι:ℝ)*∑ j,
        tailScheduleChange H d p (C j) (s j) T f (DepthAverage.coordinateProjection (e j) (τ j) q)) :=
      DepthAverage.average_mono_on _ _ _ (fun q _ => hp q)
    _ = (Fintype.card ι:ℝ)*∑ j, DepthAverage.average D (fun q =>
        tailScheduleChange H d p (C j) (s j) T f (DepthAverage.coordinateProjection (e j) (τ j) q)) := by
      rw [DepthAverage.average_mul_left,DepthAverage.average_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      let E := fun y : (C j).Vertex → Fin L => Admissible (C j) (fun v => (y v).val) d L ∧
        DepthAverage.Regular η y
      exact (DepthAverage.fiber_bound (e j) (he j) (τ j) D E (fun q hq => hD q hq j)
        (tailScheduleChange H d p (C j) (s j) T f)
        (tailScheduleChange_nonneg H d p (C j) (s j) T f)).trans
          (averaged_tailScheduleChange_le H d p hheight (C j) η hlarge (s j) E
            (fun _ h => h) T f hf)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledEvaluationContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- Before the first child branching the literal scheduled conditional mean
is exactly the martingale used in the energy theorem. All later assigned
depths stay fixed in this identity. -/
lemma scheduledPrefixMean_eq_stemMeanAt (n r d : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (hq : ∀ v, d+r≤q v) (e : Fin (r+1))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (x : FinitePath Ω (n+r)) :
    scheduledPrefixMean n r d e S q T f x=
      PrescribedTree.stemMeanAt (realize n (d+r) S q) r e T f x := by
  induction r generalizing d with
  | zero => rfl
  | succ r ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · rw [scheduledPrefixMean_zero,PrescribedTree.stemMeanAt_zero,realize_stem n (r+1) d S q hq]
    · change scheduledPrefixMean n r (d+1) e S q (T.2 x.1) (fun y => f (x.1,y)) x.2=
        PrescribedTree.stemMeanAt (realize n (d+(r+1)) S q) r e (T.2 x.1) (fun y => f (x.1,y)) x.2
      have hh := ih (d+1) (fun v => by have := hq v; omega) e (T.2 x.1) (fun y => f (x.1,y)) x.2
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

lemma scheduledProductMean_eq {ι : Type*} [Fintype ι]
    (n r d : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (hq : ∀ j v, d+r≤q j v) (e : Fin (r+1))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ) :
    scheduledProductMean n r d C q e T f=
      PrescribedTree.productStemMeanAt (fun j => realize n (d+r) (C j) (q j)) r e T f := by
  funext x i
  unfold scheduledProductMean PrescribedTree.productStemMeanAt
  apply Finset.prod_congr rfl
  intro j _
  exact scheduledPrefixMean_eq_stemMeanAt n r d (C j) (q j) (hq j) e T _ x

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ConditionalScheduledMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

lemma conditionalScheduledMean_zero (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (x : FinitePath Ω H) :
    conditionalScheduledMean H d 0 S q T f x=PrescribedTree.treeMean (realize H d S q) T f := by
  cases H <;> rfl

/-- Exact agreement with the fixed-terminal-reserve evaluation martingale. -/
lemma conditionalScheduledMean_eq_prefix (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (e : Fin (r+1)) (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ)
    (x : FinitePath Ω (n+r)) :
    conditionalScheduledMean (n+r) d e.val S q T f x=scheduledPrefixMean n r d e S q T f x := by
  induction r generalizing d with
  | zero =>
    have he : e=0 := Fin.eq_zero e
    subst e
    exact conditionalScheduledMean_zero n d S q T f x
  | succ r ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · exact conditionalScheduledMean_zero (n+(r+1)) d S q T f x
    · exact ih (d+1) e (T.2 x.1) (fun y => f (x.1,y)) x.2

/-- Exact tail-projector geometry, with the original prefix retained. -/
lemma conditionalScheduledMean_eq_tail (H p d : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → ℝ)
    (x : FinitePath Ω (H+p)) :
    conditionalScheduledMean (H+p) d p S q T f x=
      PrescribedTree.tailMean (realize H (d+p) S q) p T f x := by
  induction p generalizing d with
  | zero => exact conditionalScheduledMean_zero H d S q T f x
  | succ p ih =>
    change conditionalScheduledMean (H+p) (d+1) p S q (T.2 x.1) (fun y => f (x.1,y)) x.2=_
    have h := ih (d+1) (T.2 x.1) (fun y => f (x.1,y)) x.2
    simpa only [PrescribedTree.tailMean,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma conditionalScheduledProduct_eq_prefix {ι : Type*} [Fintype ι]
    (n r d : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (e : Fin (r+1)) (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ) :
    conditionalScheduledProduct (n+r) d e.val C q T f=scheduledProductMean n r d C q e T f := by
  funext x i
  unfold conditionalScheduledProduct scheduledProductMean
  exact Finset.prod_congr rfl (fun j _ => conditionalScheduledMean_eq_prefix n r d (C j) (q j) e T _ x)

/-- The simultaneous-schedule projector is literally this conditional
proper-child product. This is the bridge between the two continuity costs. -/
lemma conditionalScheduledProduct_eq_childSchedule {ι α : Type} [Fintype ι]
    {L : ℕ} [NeZero L] (H p : ℕ) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (s : (j : ι) → (C j).Vertex → Bool) (Q : α → Fin L)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) :
    conditionalScheduledProduct (H+p) 0 p C
      (fun j v => (DepthAverage.shiftPerm (s j v) (τ j v (Q (e j v)))).val) T f=
      childScheduleProjection H p p C e τ s T f Q := by
  funext x i
  unfold conditionalScheduledProduct childScheduleProjection scheduledTailProjection
  apply Finset.prod_congr rfl
  intro j _
  simpa only [Nat.zero_add] using conditionalScheduledMean_eq_tail H p 0 (C j)
    (fun v => (DepthAverage.shiftPerm (s j v) (τ j v (Q (e j v)))).val) T (fun y => f y i) x

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.conditionalScheduledMeanDepthDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]


lemma average_split (a : α) (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) :
    average D F=(FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
      average (fun rest => D (insertCoordinate a t rest)) (fun rest => F (insertCoordinate a t rest))) := by
  unfold average depthLaw insertCoordinate
  exact FiniteLaw.expect_pi_split _ a _

/-- Fix all child coordinates first, then average the evaluation coordinate. -/
lemma average_split_comm (a : α) (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) :
    average D F=(depthLaw {j : α // j≠a} L).expect (fun rest =>
      (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
        if D (insertCoordinate a t rest) then F (insertCoordinate a t rest) else 0)) := by
  rw [average_split a D F]
  exact FiniteLaw.expect_comm _ _ _

/-- Uniform fixed-evaluation estimates survive the unused evaluation
coordinate with no extra L factor. -/
lemma average_of_slice_le (a : α) (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) (c : ℝ)
    (h : ∀ t : Fin L, average (fun rest => D (insertCoordinate a t rest))
      (fun rest => F (insertCoordinate a t rest)) ≤ c) : average D F ≤ c := by
  rw [average_split a D F]
  exact ((FiniteLaw.uniform : FiniteLaw (Fin L)).expect_mono h).trans_eq
    (FiniteLaw.expect_const _ _)

omit [NeZero L] in
/-- Sum of a literal zero-extended prefix family. -/
lemma sum_zeroExtension {r : ℕ} (hr : r≤L) (F : Fin r → ℝ) :
    (∑ t : Fin L, if h : t.val < r then F ⟨t.val,h⟩ else 0)=∑ e : Fin r, F e := by
  classical
  let E : {t : Fin L // t.val < r} ≃ Fin r :=
    { toFun := fun t => ⟨t.1.val,t.2⟩
      invFun := fun t => ⟨⟨t.val,lt_of_lt_of_le t.isLt hr⟩,t.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ t : {t : Fin L // t.val < r}, F ⟨t.1.val,t.2⟩ := by
      rw [Finset.sum_dite]
      simp only [Finset.sum_const_zero,add_zero]
      exact (Equiv.subtypeEquivRight (by simp)).sum_comp
        (fun t : {t : Fin L // t.val < r} => F ⟨t.1.val,t.2⟩)
    _ = _ := Equiv.sum_comp E F

lemma uniform_zeroExtension {r : ℕ} (hr : r≤L) (F : Fin r → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect
      (fun t => if h : t.val < r then F ⟨t.val,h⟩ else 0)=(∑ e : Fin r, F e)/(L:ℝ) := by
  unfold FiniteLaw.expect FiniteLaw.uniform
  rw [← Finset.mul_sum,show Fintype.card (Fin L)=L from Fintype.card_fin L,sum_zeroExtension hr F]
  exact (div_eq_inv_mul _ _).symm

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ConditionalSpatialContinuity
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

noncomputable local instance instDecidable_1_r5a8952_1 (p : Prop) : Decidable p := Classical.propDecidable p
lemma projectorChangeSq_nonneg {M : ℕ} (T : KernelTower Ω M)
    (X Y : FinitePath Ω M → Fin N → ℝ) : 0≤projectorChangeSq T X Y :=
  FiniteLaw.expect_nonneg _ (fun _ => FiniteLaw.spatialSq_nonneg _)

lemma projectorChangeSq_symm {M : ℕ} (T : KernelTower Ω M)
    (X Y : FinitePath Ω M → Fin N → ℝ) : projectorChangeSq T X Y=projectorChangeSq T Y X := by
  unfold projectorChangeSq FiniteLaw.spatialSq
  simp_rw [sub_sq_comm]

lemma projectorChangeSq_triangle {M : ℕ} (T : KernelTower Ω M)
    (X Y Z : FinitePath Ω M → Fin N → ℝ) :
    projectorChangeSq T X Z≤2*(projectorChangeSq T X Y+projectorChangeSq T Y Z) := by
  have h := (KernelTower.law M T).expect_mono (fun x => show
      FiniteLaw.spatialSq (fun i => X x i-Z x i)≤
      2*(FiniteLaw.spatialSq (fun i => X x i-Y x i)+FiniteLaw.spatialSq (fun i => Y x i-Z x i)) from by
    unfold FiniteLaw.spatialSq
    calc
      _ ≤ (∑ i, 2*((X x i-Y x i)^2+(Y x i-Z x i)^2))/(N:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (X x i-2*Y x i+Z x i)]
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; ring)
  simpa only [FiniteLaw.expect_mul_left,FiniteLaw.expect_add,projectorChangeSq] using h

variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

/-- Fixed-prefix simultaneous child-shift continuity, stated on the actual
full-horizon conditional products. The horizon equality is a reindexing only. -/
theorem averaged_conditional_schedule_change_le (M H p : ℕ) (htotal : M=H+p)
    (hheight : p+H=L) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (he : ∀ j, Function.Injective (e j))
    (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : (j : ι) → (C j).Vertex → Bool)
    (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (τ j v (Q (e j v))).val) p L ∧
      DepthAverage.Regular η (DepthAverage.coordinateProjection (e j) (τ j) Q))
    (T : KernelTower Ω M) (f : FinitePath Ω M → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => projectorChangeSq T
      (conditionalScheduledProduct M 0 p C (fun j v => (τ j v (Q (e j v))).val) T f)
      (conditionalScheduledProduct M 0 p C
        (fun j v => (DepthAverage.shiftPerm (s j v) (τ j v (Q (e j v)))).val) T f)) ≤
      (Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ) := by
  subst M
  have hu (Q : α → Fin L) :
      conditionalScheduledProduct (H+p) 0 p C (fun j v => (τ j v (Q (e j v))).val) T f=
      childScheduleProjection H p p C e τ (fun _ _ => false) T f Q := by
    simpa only [DepthAverage.shiftPerm,Bool.false_eq_true,ite_false,Equiv.refl_apply] using
      conditionalScheduledProduct_eq_childSchedule H p C e τ (fun _ _ => false) Q T f
  simp_rw [hu,conditionalScheduledProduct_eq_childSchedule]
  exact averaged_childScheduleProjection_change_le H p p hheight C e he τ η hlarge s D hD T f hf

omit [NeZero L] in
/-- Full-horizon evaluation martingale energy before the first child split,
in the actual single-copy spatial norm, with arbitrary retained subdomain. -/
theorem conditional_evaluation_sum_le (M n r : ℕ) (htotal : M=n+r)
    (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (hq : ∀ j v, r≤q j v) (U : Finset (Fin r))
    (T : KernelTower Ω M) (f : FinitePath Ω M → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    (∑ t ∈ U, projectorChangeSq T
      (conditionalScheduledProduct M 0 (t.val+1) C q T f)
      (conditionalScheduledProduct M 0 t.val C q T f))/(L:ℝ) ≤ (Fintype.card ι:ℝ)^2/(L:ℝ) := by
  subst M
  have hq' : ∀ j v, 0+r≤q j v := by simpa only [Nat.zero_add] using hq
  have hs (t : Fin r) : conditionalScheduledProduct (n+r) 0 (t.val+1) C q T f=
      PrescribedTree.productStemMeanAt (fun j => realize n r (C j) (q j)) r t.succ T f := by
    have h := (conditionalScheduledProduct_eq_prefix n r 0 C q t.succ T f).trans
      (scheduledProductMean_eq n r 0 C q hq' t.succ T f)
    simpa only [Nat.zero_add,Fin.val_succ] using h
  have hb (t : Fin r) : conditionalScheduledProduct (n+r) 0 t.val C q T f=
      PrescribedTree.productStemMeanAt (fun j => realize n r (C j) (q j)) r t.castSucc T f := by
    have h := (conditionalScheduledProduct_eq_prefix n r 0 C q t.castSucc T f).trans
      (scheduledProductMean_eq n r 0 C q hq' t.castSucc T f)
    simpa only [Nat.zero_add,Fin.val_castSucc] using h
  simp_rw [hs,hb]
  unfold projectorChangeSq
  simp_rw [PrescribedTree.productStemMeanAt_spatial_increment]
  exact PrescribedTree.averaged_productStemIncrement_spatial_le
    (fun j => realize n r (C j) (q j)) r L U T f hf

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_EarliestChildDepth
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance earliestChildDepthPropDecidable_r5a8952_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {ι : Type} [Fintype ι] {L : ℕ} [NeZero L]

omit [NeZero L] in
lemma earliestChildDepth_le_horizon (C : ι → ReducedTopology)
    (q : (j : ι) → (C j).Vertex → Fin L) : earliestChildDepth C q≤L := by
  exact Nat.le_of_lt_succ (Fin.isLt _)

omit [NeZero L] in
lemma earliestChildDepth_le (C : ι → ReducedTopology)
    (q : (j : ι) → (C j).Vertex → Fin L) (j : ι) (v : (C j).Vertex) :
    earliestChildDepth C q≤(q j v).val := by
  have h : Finset.univ.inf (fun w : (j : ι) × (C j).Vertex => (q w.1 w.2).castSucc)≤
      (q j v).castSucc := Finset.inf_le (show (⟨j,v⟩ : (j : ι) × (C j).Vertex) ∈ Finset.univ from Finset.mem_univ _)
  exact h

omit [NeZero L] in
lemma lt_earliestChildDepth (C : ι → ReducedTopology)
    (q : (j : ι) → (C j).Vertex → Fin L) (t : Fin L)
    (ht : ∀ j v, t.val<(q j v).val) : t.val<earliestChildDepth C q := by
  have h : t.succ ≤ Finset.univ.inf (fun w : (j : ι) × (C j).Vertex => (q w.1 w.2).castSucc) := by
    exact Finset.le_inf (fun w _ => show t.val+1≤(q w.1 w.2).val from ht w.1 w.2)
  exact h

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullCubeConditionalContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.fullCubeConditionalPropDecidable
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]

/-- A genuine positive one-step shift is the cyclic coordinate permutation
on the regular domain; its wrap-around part is absent, not discarded. -/
theorem averaged_conditional_positive_shift_le (M H p : ℕ) (htotal : M=H+p)
    (hheight : p+H=L) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) p L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : KernelTower Ω M) (f : FinitePath Ω M → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => projectorChangeSq T
      (conditionalScheduledProduct M 0 p C (fun j v => (Q (e j v)).val+1) T f)
      (conditionalScheduledProduct M 0 p C (fun j v => (Q (e j v)).val) T f)) ≤
      (Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ) := by
  have hC (Q : α → Fin L) (hQ : D Q) :
      (fun j v => (DepthAverage.shiftPerm true (Q (e j v))).val)=
      (fun j v => (Q (e j v)).val+1) := by
    funext j v
    have hr := DepthAverage.regular_room hlarge (hD Q hQ j).2 v
    simp only [DepthAverage.shiftPerm,ite_true,DepthAverage.rotate_val_of_room _ hr]
  calc
    _ ≤ DepthAverage.average D (fun Q => projectorChangeSq T
        (conditionalScheduledProduct M 0 p C (fun j v => (Q (e j v)).val) T f)
        (conditionalScheduledProduct M 0 p C
          (fun j v => (DepthAverage.shiftPerm true (Q (e j v))).val) T f)) := by
      apply DepthAverage.average_mono_on
      intro Q hQ
      rw [hC Q hQ]
      exact (projectorChangeSq_symm T _ _).le
    _ ≤ _ := averaged_conditional_schedule_change_le M H p htotal hheight C e he
      (fun _ _ => Equiv.refl _) η hlarge (fun _ _ => true) D hD T f hf

/-- Simultaneous proper-child shift at the ACTUAL next evaluation depth,
on the full parent cube. Its spacetime marginal is a single-copy one. -/
theorem averaged_fullCube_schedule_le (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => projectorChangeSq T
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val) T f)) ≤
      (Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ) := by
  apply DepthAverage.average_of_slice_le a
  intro t
  simp only [DepthAverage.insertCoordinate_self,DepthAverage.insertCoordinate_other]
  apply averaged_conditional_positive_shift_le L (L-(t.val+1)) (t.val+1)
    (by have := t.isLt; omega) (by have := t.isLt; omega) C e he η hlarge
    (fun rest => D (DepthAverage.insertCoordinate a t rest))
  intro rest hrest j
  simpa only [DepthAverage.insertCoordinate_self,DepthAverage.insertCoordinate_other] using
    hD (DepthAverage.insertCoordinate a t rest) hrest j
  exact hf

/-- Change the common evaluation depth back by one in the same physical
path, while EVERY proper-child branching coordinate is fixed. The terminal
case of leaf children uses a full unary stretch of length L. -/
theorem averaged_fullCube_evaluation_le (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j v, (Q a).val<(Q (e j v)).val)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => projectorChangeSq T
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val) T f)
      (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f)) ≤
      (Fintype.card ι:ℝ)^2/(L:ℝ) := by
  rw [DepthAverage.average_split_comm a]
  apply le_trans (FiniteLaw.expect_mono _ (fun rest => ?_)) (FiniteLaw.expect_const _ _).le
  simp only [DepthAverage.insertCoordinate_self,DepthAverage.insertCoordinate_other]
  let q := fun j v => rest (e j v)
  let r := earliestChildDepth C q
  have hr : r≤L := earliestChildDepth_le_horizon C q
  let F := fun t : ℕ => projectorChangeSq T
    (conditionalScheduledProduct L 0 (t+1) C (fun j v => (q j v).val) T f)
    (conditionalScheduledProduct L 0 t C (fun j v => (q j v).val) T f)
  change (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
    if D (DepthAverage.insertCoordinate a t rest) then F t.val else 0)≤_
  calc
    _ ≤ (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t => if h : t.val < r then F t.val else 0) := by
      apply FiniteLaw.expect_mono
      intro t
      by_cases ht : D (DepthAverage.insertCoordinate a t rest)
      · have htr : t.val < r := lt_earliestChildDepth C q t (by
          intro j v
          simpa only [DepthAverage.insertCoordinate_self,DepthAverage.insertCoordinate_other] using
            hD (DepthAverage.insertCoordinate a t rest) ht j v)
        simp only [ht,ite_true,htr,dite_eq_left]
        exact le_rfl
      · simp only [ht,ite_false]
        split_ifs
        · exact projectorChangeSq_nonneg T _ _
        · exact le_rfl
    _ = (∑ t : Fin r, F t.val)/(L:ℝ) := DepthAverage.uniform_zeroExtension hr (fun t => F t.val)
    _ ≤ _ := by
      simpa only [F] using conditional_evaluation_sum_le L (L-r) r (by omega) C
        (fun j v => (q j v).val) (earliestChildDepth_le C q) Finset.univ T f hf

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProjectionShiftError
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.projectionShiftAveragePropDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_add_eq (D : (α → Fin L) → Prop) (F G : (α → Fin L) → ℝ) :
    average D (fun Q => F Q+G Q)=average D F+average D G := by
  unfold average
  rw [← FiniteLaw.expect_add]
  apply FiniteLaw.expect_congr
  intro Q
  split_ifs <;> ring

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance projectionShiftErrorPropDecidable_r5a8952_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]


omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_nonneg (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (Q : α → Fin L) :
    0≤projectionShiftError a C e T f Q := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_sq (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (Q : α → Fin L) :
    (projectionShiftError a C e T f Q)^2=4*projectorChangeSq T
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
      (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f) := by
  unfold projectionShiftError
  rw [mul_pow,Real.sq_sqrt (projectorChangeSq_nonneg T _ _)]
  norm_num

/-- Literal normalized regular-assignment estimate (projection-shift-error).
Constants depend ONLY on the reduced child topologies, not on kernels,
spatial dimension, depth count, target histories, or extension choices. -/
theorem averaged_projectionShiftError_sq_le (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => (projectionShiftError a C e T f Q)^2) ≤
      8*((Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)+(Fintype.card ι:ℝ)^2)/(L:ℝ) := by
  have hsum := add_le_add
    (averaged_fullCube_schedule_le a C e he η hlarge D hD T f hf)
    (averaged_fullCube_evaluation_le a C e D (fun Q hQ j v =>
      admissible_lower (C j) _ (hD Q hQ j).1 v) T f hf)
  simp_rw [← Finset.sum_div] at hsum
  have htriangle : DepthAverage.average D (fun Q =>
      projectorChangeSq T
        (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
        (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f)) ≤
      2*(DepthAverage.average D (fun Q => projectorChangeSq T
        (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
        (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val) T f))+
        DepthAverage.average D (fun Q => projectorChangeSq T
        (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val) T f)
        (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f))) := by
    rw [← DepthAverage.average_add_eq,← DepthAverage.average_mul_left]
    apply DepthAverage.average_mono_on
    intro Q _
    exact projectorChangeSq_triangle T _ _ _
  simp_rw [projectionShiftError_sq]
  rw [DepthAverage.average_mul_left]
  exact (mul_le_mul_of_nonneg_left
    (htriangle.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))) (by norm_num)).trans_eq (by ring)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProjectionShiftError
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open _root_.MeasureTheory
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.rootProjectionShiftErrorDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_le_sqrt_average_sq (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    (hF : ∀ Q, D Q → 0≤F Q) : average D F≤Real.sqrt (average D (fun Q => (F Q)^2)) := by
  have h := FiniteLaw.expect_sqrt_le (depthLaw α L)
    (fun Q => if D Q then (F Q)^2 else 0) (fun Q => by split_ifs <;> positivity)
  have he : (fun Q => Real.sqrt (if D Q then (F Q)^2 else 0))=(fun Q => if D Q then F Q else 0) := by
    funext Q
    split_ifs with hQ
    · exact Real.sqrt_sq (hF Q hQ)
    · exact Real.sqrt_zero
  rw [he] at h
  exact h

lemma integrable_average {Z : Type} [MeasurableSpace Z] {μ : Measure Z}
    (D : (α → Fin L) → Prop) (F : Z → (α → Fin L) → ℝ)
    (hF : ∀ Q, Integrable (fun z => F z Q) μ) : Integrable (fun z => average D (F z)) μ := by
  unfold average FiniteLaw.expect
  apply integrable_finsetSum
  intro Q _
  by_cases hQ : D Q
  · simpa only [ite_eq_left hQ] using (hF Q).const_mul ((depthLaw α L).weight Q)
  · simp only [ite_eq_right hQ,mul_zero]
    exact integrable_zero Z ℝ μ

lemma integral_average {Z : Type} [MeasurableSpace Z] {μ : Measure Z}
    (D : (α → Fin L) → Prop) (F : Z → (α → Fin L) → ℝ)
    (hF : ∀ Q, Integrable (fun z => F z Q) μ) :
    (∫ z, average D (F z) ∂μ)=average D (fun Q => ∫ z, F z Q ∂μ) := by
  have hG (Q : α → Fin L) : Integrable (fun z => if D Q then F z Q else 0) μ := by
    by_cases hQ : D Q
    · simpa only [ite_eq_left hQ] using hF Q
    · simp only [ite_eq_right hQ]; exact integrable_zero Z ℝ μ
  unfold average FiniteLaw.expect
  rw [integral_finsetSum Finset.univ (fun Q _ => (hG Q).const_mul _)]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hQ : D Q <;> simp only [hQ,ite_true,ite_false,integral_zero]

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory
open scoped BigOperators
variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] {L N : ℕ} [NeZero L]

theorem averaged_projectionShiftError_le {Ω : Type} [Fintype Ω]
    (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (projectionShiftError a C e T f) ≤
      Real.sqrt (8*((Fintype.card ι:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(Fintype.card ι:ℝ)^2)/(L:ℝ)) :=
  (DepthAverage.average_le_sqrt_average_sq D _ (fun Q _ => projectionShiftError_nonneg a C e T f Q)).trans
    (Real.sqrt_le_sqrt (averaged_projectionShiftError_sq_le a C e he η hlarge D hD T f hf))

/-- The SAME normalized-cube estimate survives genuine physical-root
averaging with no uniformity loss. The root law may have a variable finite
alphabet. Only ordinary Bochner integrability is required. -/
theorem root_averaged_projectionShiftError_le_sat_oai {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : (z : Z) → KernelTower (Ω z) L)
    (f : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) (hf : ∀ z x i, |f z x i|≤1)
    (hI : ∀ Q, Integrable (fun z => projectionShiftError a C e (T z) (f z) Q) μ) :
    DepthAverage.average D (fun Q => ∫ z, projectionShiftError a C e (T z) (f z) Q ∂μ) ≤
      Real.sqrt (8*((Fintype.card ι:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(Fintype.card ι:ℝ)^2)/(L:ℝ)) := by
  rw [← DepthAverage.integral_average D _ hI]
  have h := integral_mono (DepthAverage.integrable_average D _ hI) (integrable_const _) (fun z =>
    averaged_projectionShiftError_le a C e he η hlarge D hD (T z) (f z) (hf z))
  simpa only [integral_const,probReal_univ,one_smul] using h

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.ReducedTopology.root_averaged_projectionShiftError_le_sat_oai := @OAI.DilutedSpinGlass.ReducedTopology.root_averaged_projectionShiftError_le_sat_oai
