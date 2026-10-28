-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.physicalShapeLimsup_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:05:40.935833+00:00
-- url     : https://prove2.me/submissions/c9abb202-6c80-4daf-b617-0dd43841cfa8

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physical_grid_scheduled_step

section
-- module Solutions.OAIQ041_DS.Compat
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

theorem expect_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : P.expect f = P.expect g := by
  exact congrArg P.expect (funext h)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

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

theorem abs_expect_le {f : Ω → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |P.expect f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).1)
    simpa only [expect_const] using h
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).2)
    simpa only [expect_const] using h

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProducts
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeDerivatives
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
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

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Perturbations
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_HistoryGeometry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

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

noncomputable local instance instDecidable_6_r33125b_1 (p : Prop) : Decidable p := Classical.propDecidable p
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

theorem branchProduct_succ (x y : ℝ) {k : ℕ} (hk : 0 < k) :
    branchProduct x y (k+1) = branchProduct x y k * (x-(k:ℝ)*y) := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  simp [branchProduct, Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]


attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidableEqLeaf_1
noncomputable local instance (priority := 2000) instDecidableEqSigma_r33125b_1 {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _
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

private theorem prod_local_factor {α : Type*} [Fintype α] (f g : α → ℝ) (i : α) (c : ℝ)
    (hi : f i = c*g i) (ho : ∀ j, j ≠ i → f j = g j) :
    (∏ j, f j) = c*∏ j, g j := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),hi]
  have he : (∏ j ∈ Finset.univ.erase i, f j) = ∏ j ∈ Finset.univ.erase i, g j :=
    Finset.prod_congr rfl (fun j hj => ho j (Finset.mem_erase.mp hj).1)
  rw [he,mul_assoc]

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidableEqLeaf_2
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

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_11
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

theorem chargeBound_nonneg {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (k b : ℕ) :
    0 ≤ chargeBound C D k b := by
  induction k generalizing b with
  | zero => simp only [chargeBound]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero => exact mul_nonneg hC (ih 0)
    | succ b => exact add_nonneg (mul_nonneg hC (ih _)) (mul_nonneg hD (ih _))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SplitDepthContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
    exact hi
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SizeSpinRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualPrefix
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcentrationRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology BigOperators

lemma unit_limsup_nonneg {f : ℕ → ℝ} (h0 : ∀ n, 0≤f n) (h1 : ∀ n, f n≤1) :
    0≤limsup f atTop := by
  apply le_limsup_of_le (show IsBoundedUnder (·≤·) atTop f from
    isBoundedUnder_of_eventually_le (Eventually.of_forall h1))
  intro b hb
  obtain ⟨n,hn⟩ := hb.exists
  exact (h0 n).trans hn

/-- A finite-family limsup estimate, proved by taking the size limit before
removing the positive scalar slack. No uniform size rate is used. -/
lemma limsup_finite_sqrt_bound {ι : Type*} [Fintype ι]
    (a e : ℕ → ℝ) (f : ι → ℕ → ℝ) {η b c k : ℝ}
    (hη : 0<η) (hc : 0 ≤ c) (hk : 0≤k)
    (ha0 : ∀ n, 0≤a n) (ha1 : ∀ n, a n≤1)
    (hf1 : ∀ j n, f j n≤1) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ n, η*a n≤b+2*e n+c*Real.sqrt (k*∑ j, Real.sqrt (f j n))) :
    η*limsup a atTop≤b+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop)) := by
  classical
  have hcap (t : ℝ) (ht : 0<t) :
      η*limsup a atTop≤b+2*t+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop+t)) := by
    have hef : ∀ᶠ n in atTop, e n<t := he.eventually (Iio_mem_nhds ht)
    have hff : ∀ᶠ n in atTop, ∀ j, f j n<limsup (f j) atTop+t := by
      apply eventually_all.mpr
      intro j
      exact eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht)
        (isBoundedUnder_of_eventually_le (Eventually.of_forall (hf1 j)))
    have hab : ∀ᶠ n in atTop, a n≤
        (b+2*t+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop+t)))/η := by
      filter_upwards [hef,hff] with n hen hfn
      apply (le_div_iff₀ hη).mpr
      rw [mul_comm]
      apply (hbound n).trans
      apply add_le_add
      · linarith
      · apply mul_le_mul_of_nonneg_left _ hc
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left _ hk
        exact Finset.sum_le_sum (fun j _ => Real.sqrt_le_sqrt (hfn j).le)
    have hl := (limsup_le_iff
      (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha0).frequently))
      (isBoundedUnder_of_eventually_le (Eventually.of_forall ha1))).mpr
        (fun bound hbound => hab.mono (fun _ hle => hle.trans_lt hbound))
    simpa only [mul_comm η] using (le_div_iff₀ hη).mp hl
  have htend : Tendsto
      (fun t : ℝ => b+2*t+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop+t)))
      (𝓝[>] 0) (𝓝 (b+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop)))) := by
    have hcont : ContinuousAt
        (fun t : ℝ => b+2*t+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop+t))) 0 := by
      fun_prop
    simpa using hcont.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall (fun t ht => hcap t ht))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FinitePiInjective
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinRootData
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularDepth
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance regularDepthPropDecidable_r33125b_1 (proposition : Prop) : Decidable proposition :=
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

lemma normalized_shift_bounds (s : Bool) (q : Fin L) (hq : q.val+1<L) :
    normalized q ≤ normalized (shiftPerm s q) ∧
    normalized (shiftPerm s q) ≤ normalized q + 1/(L:ℝ) := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  cases s with
  | false =>
    simp only [shiftPerm,Bool.false_eq_true,ite_false,Equiv.refl_apply]
    constructor
    · exact le_rfl
    · linarith [one_div_pos.mpr hL]
  | true =>
    simp only [shiftPerm,ite_true,normalized,rotate_val_of_room q hq,Nat.cast_add,Nat.cast_one]
    constructor
    · exact div_le_div_of_nonneg_right (by linarith) hL.le
    · rw [add_div]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Positive shifts of any subset of retained coordinates are truly +1,
not modular wraparound, and send the regular domain into η/2 regularity.
The fixed numerical threshold is deliberately generous and uniform. -/
theorem regular_shift_restrict {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L:ℝ))
    (e : β → α) (he : Function.Injective e) (s : β → Bool)
    {q : α → Fin L} (hq : Regular η q) :
    Regular (η/2) (coordinateProjection e (fun i => shiftPerm (s i)) q) := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hstep : 1/(L:ℝ)<η/4 := (div_lt_iff₀ hL).mpr (by nlinarith)
  have hb (i : β) := normalized_shift_bounds (s i) (q (e i))
    (regular_room (by linarith : 1<η*(L:ℝ)) hq (e i))
  constructor
  · intro i
    change η/2 < normalized (shiftPerm (s i) (q (e i))) ∧
      normalized (shiftPerm (s i) (q (e i))) < 1-η/2
    have hi := hq.1 (e i)
    constructor <;> linarith [hb i]
  · intro i j hij
    change η/2 < |normalized (shiftPerm (s i) (q (e i)))-
      normalized (shiftPerm (s j) (q (e j)))|
    have hi := hb i
    have hj := hb j
    have hold := hq.2 (e i) (e j) (fun heq => hij (he heq))
    have htri := abs_sub_le (normalized (q (e i)))
      (normalized (shiftPerm (s i) (q (e i)))) (normalized (q (e j)))
    have htri2 := abs_sub_le (normalized (shiftPerm (s i) (q (e i))))
      (normalized (shiftPerm (s j) (q (e j)))) (normalized (q (e j)))
    have hd1 : |normalized (q (e i))-normalized (shiftPerm (s i) (q (e i)))| ≤ 1/(L:ℝ) :=
      abs_le.mpr ⟨by linarith,by linarith⟩
    have hd2 : |normalized (shiftPerm (s j) (q (e j)))-normalized (q (e j))| ≤ 1/(L:ℝ) :=
      abs_le.mpr ⟨by linarith,by linarith⟩
    linarith

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalIndex
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

theorem abs_spin (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProfileHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance kappaRegularDecidable_r33125b_1 (p : Prop) : Decidable p :=
  Classical.propDecidable p
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

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.kappaRegularLeafDecidableEq
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
-- module Solutions.OAIQ041_DS.DilutedSpin_GlobalSelectedAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

noncomputable local instance pairObservableHistoryDecidable_r33125b_1 (proposition : Prop) :
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
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeMeasurable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixPair
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

noncomputable local instance matrixPairPropDecidable_r33125b_1 (proposition : Prop) : Decidable proposition :=
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

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UniformRootDecorrelation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

/-- Unlike a bound by all grid vertices, the exact full history mass is
uniform in the number of unary levels. -/
lemma pairHistoryMass_grid (hL : 0<L) (S : PrescribedTree L) (a : S.Leaf) :
    pairHistoryMass S (grid L 0 L) a=2*(leaves S:ℝ)-1 := by
  unfold pairHistoryMass
  rw [sum_abs_gamma_grid hL S,Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,card_leaf]
  have hp : 1≤leaves S := by
    rw [← card_leaf]
    exact Fintype.card_pos_iff.mpr ⟨a⟩
  rw [Nat.cast_sub hp]
  simp only [Nat.cast_one]
  ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixConstant
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable local instance partialKappaPairDecidable_r33125b_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
lemma partialKappa_pair (T : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a b : T.Leaf) (hab : a ≠ b) :
    partialKappa T m {b,a} =
      m ⟨splitDepth T a b,by have := splitDepth_lt_of_ne T a b hab; omega⟩-
      m ⟨splitDepth T a b+1,by have := splitDepth_lt_of_ne T a b hab; omega⟩ := by
  classical
  have h := matrix_choice_kappa T T id Function.injective_id {a} (Finset.singleton_nonempty _)
    b (by simpa using hab.symm) (fun _ => a) (Finset.univ.erase a) id
    (singleton_history_cover T a a)
    (by intro c hc d hd; have hc' := Finset.mem_singleton.mp hc; have hd' := Finset.mem_singleton.mp hd
        subst c; subst d; rfl) m hm hp hend
  simp only [Finset.mem_singleton,forall_eq,id_eq,Finset.image_id,partialKappa_singleton,div_one] at h
  simp_rw [splitDepth_symm T _ a] at h
  have he (v : T.Internal) : freshSplitDepth T v a = splitDepth (grow T v) (oldLeaf T v a) (newLeaf T v) := by
    rw [splitDepth_symm,splitDepth_new_old]
  simp_rw [he] at h
  rw [pair_univ_erase T a (splitDepth T a b) (splitDepth_lt_of_ne T a b hab),
    pair_choice_total T a (splitDepth T a b) (splitDepth_lt_of_ne T a b hab) m hend] at h
  exact h.symm

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

noncomputable local instance matrixEnergyPropDecidable_r33125b_1 (proposition : Prop) :
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

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance kappaLowerDecidable_r33125b_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
lemma branchProduct_lower {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (hy : η ≤ y) (k : ℕ) :
    (y-x)*η^k ≤ |branchProduct x y (k+2)| := by
  classical
  induction k with
  | zero =>
    simp only [pow_zero,mul_one,branchProduct,show (2:ℕ)-1 = 1 from rfl,Finset.prod_range_one,Nat.cast_zero,zero_add,one_mul]
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 by omega,branchProduct_succ x y (by omega),abs_mul,pow_succ]
    have hh : η ≤ |x-((k+2:ℕ):ℝ)*y| := by
      have hY : 0 ≤ y := hη.trans hy
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have hmul := mul_nonneg hk hY
      have hn : x-((k+2:ℕ):ℝ)*y ≤ 0 := by push_cast; nlinarith
      rw [abs_of_nonpos hn]
      push_cast
      nlinarith
    simpa only [mul_assoc] using mul_le_mul ih hh hη (abs_nonneg _)

lemma branchProduct_lower_pos {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (hy : η ≤ y)
    (k : ℕ+) :
    (y-x)^(if 1 < (k:ℕ) then 1 else 0)*η^((k:ℕ)-2) ≤ |branchProduct x y k| := by
  classical
  have hk := k.property
  by_cases h : 1 < (k:ℕ)
  · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 2 ≤ (k:ℕ) by omega)
    have hkj : (k:ℕ) = j+2 := by omega
    simp only [ite_eq_left h,pow_one]
    rw [hkj]
    simp only [Nat.add_sub_cancel]
    exact branchProduct_lower hxy hη hy j
  · have hle : (k:ℕ) ≤ 1 := le_of_not_gt h
    have he : (k:ℕ) = 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt hk)
    simp [he]

lemma leaf_nonempty {n : ℕ} (S : PrescribedTree n) : Nonempty S.Leaf := by
  induction S with
  | leaf => exact ⟨()⟩
  | @node n k C ih =>
    obtain ⟨a⟩ := ih ⟨0,k.property⟩
    exact ⟨⟨⟨0,k.property⟩,a⟩⟩

noncomputable local instance kappaLowerLeafDecidableEq_r33125b_1 {depth : ℕ} (tree : PrescribedTree depth) :
    DecidableEq tree.Leaf := Classical.decEq _
lemma childRefs_univ {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n) (i : Fin k) :
    childRefs (C := C) Finset.univ i = Finset.univ := by
  classical
  ext a
  rw [mem_childRefs]
  exact iff_of_true (Finset.mem_univ _) (Finset.mem_univ _)

lemma partialKappa_univ_node {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n)
    (m : Fin (n+2) → ℝ) :
    partialKappa (.node k C) m Finset.univ = branchProduct (m 0) (m 1) k *
      ∏ i, partialKappa (C i) (fun j => m j.succ) Finset.univ := by
  classical
  rw [partialKappa]
  have he : Finset.image (fun a : Leaf (.node k C) => a.1) Finset.univ = Finset.univ := by
    ext i
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    obtain ⟨a⟩ := leaf_nonempty (C i)
    exact ⟨⟨i,a⟩,rfl⟩
  rw [he]
  simp only [Finset.card_univ,Fintype.card_fin,childRefs_univ]

lemma branchProduct_lower_regular {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (k : ℕ+)
    (hy : 2 < (k:ℕ) → η ≤ y) :
    (y-x)^(if 1 < (k:ℕ) then 1 else 0)*η^((k:ℕ)-2) ≤ |branchProduct x y k| := by
  classical
  by_cases hk : 2 < (k:ℕ)
  · exact branchProduct_lower_pos hxy hη (hy hk) k
  · have hp := k.property
    have hle : (k:ℕ) ≤ 2 := le_of_not_gt hk
    have he : (k:ℕ) = 1 ∨ (k:ℕ) = 2 := by
      rcases Nat.lt_or_eq_of_le hle with hs | hs
      · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hs) (Nat.succ_le_of_lt hp))
      · exact Or.inr hs
    rcases he with he|he
    · simp [he]
    · simp only [he,show 1 < (2:ℕ) from by omega,ite_true,pow_one,Nat.sub_self,pow_zero,mul_one]
      simp only [branchProduct,show (2:ℕ)-1 = 1 from rfl,Finset.prod_range_one,Nat.cast_zero,zero_add,one_mul]
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith

 
theorem partialKappa_grid_lower {n : ℕ} (S : PrescribedTree n) (d L : ℕ)
    (η : ℝ) (hη : 0 ≤ η) (hr : BranchRegular S (grid n d L) η) :
    (L:ℝ)⁻¹^(branchingCount S (fun _ => True))*η^(branchExcess S) ≤
      |partialKappa S (grid n d L) Finset.univ| := by
  classical
  induction S generalizing d with
  | leaf => simp [partialKappa,branchingCount,branchExcess]
  | @node n k C ih =>
    have he : (fun j : Fin (n+1) => grid (n+1) d L j.succ) = grid n (d+1) L := by
      funext j
      simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
    have hr' : (2 < (k:ℕ) → η ≤ grid (n+1) d L 1) ∧
        ∀ i, BranchRegular (C i) (grid n (d+1) L) η := by
      simpa only [BranchRegular,he] using hr
    have hδ : grid (n+1) d L 1-grid (n+1) d L 0 = (L:ℝ)⁻¹ := by
      simp [grid,Nat.cast_add,add_div]
    have hle : grid (n+1) d L 0 ≤ grid (n+1) d L 1 := by
      have hnonneg : (0:ℝ) ≤ (L:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg L)
      linarith
    have hroot := branchProduct_lower_regular hle hη k hr'.1
    rw [hδ] at hroot
    have hchild := Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
      mul_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg L)) _) (pow_nonneg hη _))
      (fun i _ => ih i (d+1) (hr'.2 i))
    have h := mul_le_mul hroot hchild
      (Finset.prod_nonneg (fun i _ => mul_nonneg
        (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg L)) _) (pow_nonneg hη _))) (abs_nonneg _)
    rw [partialKappa_univ_node,abs_mul,Finset.abs_prod,he]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [branchingCount,branchExcess,true_and,pow_add,Finset.prod_mul_distrib,← Finset.prod_pow_eq_pow_sum]
    ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootMatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {L : ℕ}

lemma partialKappa_grid_pair (hL : 0 < L) (T : PrescribedTree L)
    (a b : T.Leaf) (hab : a ≠ b) :
    partialKappa T (grid L 0 L) {b,a} = -(L:ℝ)⁻¹ := by
  rw [partialKappa_pair T _ (grid_strictMono hL) grid_nonneg (grid_last hL) a b hab]
  simp [grid,Nat.cast_add,add_div]

/-- The separation vertex is the protected pair factor, leaving exactly the
powers charged at the shifted internal branching vertices. -/
theorem protectedKappa_grid_lower (hL : 0 < L) (T : PrescribedTree L)
    (a b : T.Leaf) (hab : a ≠ b) (η : ℝ) (hη : 0 ≤ η)
    (hr : BranchRegular T (grid L 0 L) η) (k : ℕ)
    (hk : branchingCount T (fun _ => True) = k+1) :
    (L:ℝ)⁻¹^k*η^(branchExcess T) ≤
      |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}| := by
  have hδ : 0 < (L:ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hL)
  rw [abs_div,partialKappa_grid_pair hL T a b hab,abs_neg,abs_of_pos hδ]
  apply (le_div_iff₀ (inv_pos.mpr (Nat.cast_pos.mpr hL))).mpr
  have h := partialKappa_grid_lower T 0 L η hη hr
  rw [hk,pow_succ] at h
  nlinarith [h]

/-- The manuscript's relative absolute-cost bound. Its dimensional power of
L cancels EXACTLY, including distinct target vertices sharing a depth. -/
theorem shiftedCharge_relative_bound (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (k : ℕ) (a b : T.Leaf) (hab : a ≠ b)
    (η : ℝ) (hη : 0 < η) (hr : BranchRegular T (grid L 0 L) η)
    (hb : branchingCount T (fun _ => True) = branchingCount T (· ∈ Q)+1) :
    shiftedCharge Q T S k /
        |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}| ≤
      chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k
        (branchingCount T (· ∈ Q)) / η^(branchExcess T) := by
  let J := |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}|
  let A := chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k
    (branchingCount T (· ∈ Q))
  let D := (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
  let E := η^(branchExcess T)
  have hD : 0 < D := pow_pos (inv_pos.mpr (Nat.cast_pos.mpr hL)) _
  have hE : 0 < E := pow_pos hη _
  have hA : 0 ≤ A := chargeBound_nonneg (by positivity) (by positivity) _ _
  have hlo : D*E ≤ J := protectedKappa_grid_lower hL T a b hab η hη.le hr _ hb
  have hJ : 0 < J := (mul_pos hD hE).trans_le hlo
  change A*D/J ≤ A/E
  apply (div_le_div_iff₀ hJ hE).mpr
  have hh := mul_le_mul_of_nonneg_left hlo hA
  nlinarith [hh]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeProjectionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

lemma shapeEnergyAt_nonneg (C : PrescribedTree n) (d : ℕ) (T : KernelTower Ω (n+1+d))
    (f : FinitePath Ω (n+1+d) → Fin N → ℝ) : 0 ≤ shapeEnergyAt C d T f := by
  induction d with
  | zero => unfold shapeEnergyAt childEnergy FiniteLaw.covarianceEnergy; positivity
  | succ d ih => exact T.1.expect_nonneg (fun z => ih (T.2 z) (fun y => f (z,y)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShiftedTree
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.shiftedTreeDecidable
lemma branchingCount_unary {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount (unary S) P = branchingCount S (fun d => P (d+1)) := by
  classical
  change (if P 0 ∧ 1 < (1:ℕ) then 1 else 0)+
    (∑ _ : Fin 1, branchingCount S (fun d => P (d+1))) = _
  simp

lemma leaves_bottom {n : ℕ} (S : PrescribedTree n) : leaves (bottomUnary S) = leaves S := by
  induction S with
  | leaf =>
    change (∑ _ : Fin 1, (1:ℕ)) = 1
    simp
  | @node n k C ih => simp only [bottomUnary,leaves,ih]

lemma leaves_unary {n : ℕ} (S : PrescribedTree n) : leaves (unary S) = leaves S := by
  change (∑ _ : Fin 1, leaves S) = _
  simp

/-- Literal branching-vertex count as a sum. Distinct vertices at equal
depths occur separately; no count by distinct depth values is substituted. -/
lemma branchingCount_eq_vertexSum {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount S P = ∑ v : S.Internal,
      if 1 < vertexArity S v ∧ P (vertexDepth S v) then 1 else 0 := by
  classical
  induction S generalizing P with
  | leaf =>
    change 0 = ∑ v : Empty, _
    simp
  | @node n k C ih =>
    change _ = ∑ v : Option ((i : Fin k) × Internal (C i)), _
    rw [Fintype.sum_option]
    simp only [vertexArity,vertexDepth,Fintype.sum_sigma,branchingCount,ih,and_comm]

lemma mem_branchingDepths {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    d ∈ branchingDepths S ↔ ∃ v : S.Internal, 1 < vertexArity S v ∧ vertexDepth S v=d := by
  classical
  simp only [branchingDepths,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

lemma branchingCount_congr_on {n : ℕ} (S : PrescribedTree n) (P Q : ℕ → Prop)
    (h : ∀ d ∈ branchingDepths S, P d ↔ Q d) : branchingCount S P = branchingCount S Q := by
  classical
  rw [branchingCount_eq_vertexSum,branchingCount_eq_vertexSum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : 1 < vertexArity S v
  · have hd := h (vertexDepth S v) ((mem_branchingDepths S _).mpr ⟨v,hv,rfl⟩)
    simp only [hv,true_and,hd]
  · simp only [hv,false_and,ite_false]


lemma zero_not_mem_shiftedTwinDepths {n : ℕ} (S : PrescribedTree n) :
    0 ∉ shiftedTwinDepths S := by
  classical
  simp [shiftedTwinDepths]

lemma shifted_twin_target_count {n : ℕ} (S : PrescribedTree n) :
    branchingCount (doubled (unary S)) (· ∈ shiftedTwinDepths S) =
      2*branchingCount S (fun _ => True) := by
  classical
  have hC : branchingCount S (fun d => d+1+1 ∈ shiftedTwinDepths S) =
      branchingCount S (fun _ => True) := by
    apply branchingCount_congr_on
    intro d hd
    exact iff_of_true (Finset.mem_image.mpr ⟨d,hd,by omega⟩) trivial
  simp only [doubled,branchingCount]

  simp only [zero_not_mem_shiftedTwinDepths,false_and,ite_false,branchingCount_unary,hC,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,zero_add]
  norm_num

lemma shifted_twin_total_count {n : ℕ} (S : PrescribedTree n) :
    branchingCount (doubled (unary S)) (fun _ => True) =
      branchingCount (doubled (unary S)) (· ∈ shiftedTwinDepths S)+1 := by
  classical
  rw [shifted_twin_target_count]
  simp only [doubled,branchingCount]

  simp only [branchingCount_unary,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num at *
  omega

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledTopology
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

lemma realize_leaves (r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : Admissible S q d (d+r)) :
    PrescribedTree.leaves (realize r d S q) = Fintype.card S.Leaf := by
  induction r generalizing d S with
  | zero =>
    cases S with
    | leaf => rfl
    | node k hk C => have := h.2.1; have := h.1; omega
  | succ r ih =>
    cases S with
    | leaf =>
      rw [realize,PrescribedTree.leaves_unary]
      exact ih (d+1) .leaf q trivial
    | node k hk C =>
      rw [realize]
      split_ifs with hd
      · rw [PrescribedTree.leaves_unary]
        apply ih
        exact ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩
      · have he : q none=d := by have := h.1; omega
        simp only [PrescribedTree.leaves]
        change _ = Fintype.card ((i : Fin k) × (C i).Leaf)
        rw [Fintype.card_sigma]
        apply Finset.sum_congr rfl
        intro i _
        apply ih
        simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2.2 i

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
      convert hh using 1 <;> first | rfl | simp only [Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
      all_goals rfl

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
-- module Solutions.OAIQ041_DS.DilutedSpin_VertexContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.realizeTranslationDecidable
lemma realize_translate (H d a : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) :
    realize H (d+a) S (fun v => q v+a)=realize H d S q := by
  induction H generalizing d S with
  | zero => rfl
  | succ H ih =>
    cases S with
    | leaf =>
      simp only [realize]
      rw [show d+a+1=(d+1)+a by omega, ih]
    | node k hk C =>
      simp only [realize, Nat.add_lt_add_iff_right]
      split_ifs with hd
      · rw [show d+a+1=(d+1)+a by omega,ih]
      · congr 1
        funext i
        rw [show d+a+1=(d+1)+a by omega,ih]

/-- Bottom extension preserves all assigned internal depths, and supplies
precisely the old tree used opposite a delayed target in the matrix identity. -/
theorem realize_bottom (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q d (d+H)) :
    realize (H+1) d S q=PrescribedTree.bottomUnary (realize H d S q) := by
  induction H generalizing d S with
  | zero =>
    cases S with
    | leaf => rfl
    | node k hk C => have := hq.1; have := hq.2.1; omega
  | succ H ih =>
    cases S with
    | leaf =>
      simp only [realize,PrescribedTree.unary,PrescribedTree.bottomUnary]
      congr 1
      funext i
      exact ih (d+1) .leaf q trivial
    | node k hk C =>
      conv_lhs => rw [realize]
      conv_rhs => arg 1; rw [realize]
      split_ifs with hd
      · change PrescribedTree.node 1 _=PrescribedTree.node 1 _
        congr 1
        funext i
        apply ih
        exact ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq.2⟩
      · simp only [PrescribedTree.bottomUnary]
        congr 1
        funext i
        apply ih
        have he : q none=d := by have := hq.1; omega
        simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq.2.2 i

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AdmissibleInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

noncomputable local instance admissibleIntervalPropDecidable_r33125b_1 (proposition : Prop) :
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
-- module Solutions.OAIQ041_DS.DilutedSpin_StemCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

lemma leaf_card_pos (S : ReducedTopology) : 0<Fintype.card S.Leaf := by
  induction S with
  | leaf => exact Nat.zero_lt_one
  | node k hk C ih =>
    change 0<Fintype.card ((j : Fin k) × (C j).Leaf)
    rw [Fintype.card_sigma]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨⟨0,k.property⟩,Finset.mem_univ _,ih _⟩

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DoubledStemProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

lemma splitDepth_stem (S : PrescribedTree n) (r : ℕ) (a b : S.Leaf) :
    splitDepth (stem S r) (stemLeaf S r a) (stemLeaf S r b)=splitDepth S a b+r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change splitDepth (.node 1 (fun _ => stem S r)) ⟨0,stemLeaf S r a⟩ ⟨0,stemLeaf S r b⟩=_
    rw [splitDepth_same_child,ih]
    omega

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CoordinateFiber
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance instDecidable_solutions_1_r33125b_1 (p : Prop) : Decidable p := Classical.propDecidable p
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MultileafMatrixPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

lemma splitFrame_split (S : PrescribedTree n) (r d : ℕ) (a : S.Leaf) :
    splitDepth (splitFrame S r d) (splitFrameLeaf S r d 0 a) (splitFrameLeaf S r d 1 a)=d := by
  exact (splitDepth_stem (doubled (stem S r)) d
    ⟨0,stemLeaf S r a⟩ ⟨1,stemLeaf S r a⟩).trans
    (by
      exact (congrArg (fun x => x+d)
        (splitDepth_diff_child (fun _ : Fin (2:ℕ+) => stem S r) 0 1 (by decide)
          (a := stemLeaf S r a) (b := stemLeaf S r a))).trans (Nat.zero_add d))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularScheduleShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

noncomputable local instance regularScheduleShiftPropDecidable_r33125b_1 (proposition : Prop) :
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SimultaneousShift
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SpatialScheduledContinuity
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductEvaluationContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_TargetEvaluationContinuity
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
-- module Solutions.OAIQ041_DS.DilutedSpin_TargetScheduleContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ProperChildScheduleContinuity
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledEvaluationContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ConditionalScheduledMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

lemma conditionalScheduledMean_bound (H d e : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x|≤1) (x : FinitePath Ω H) :
    |conditionalScheduledMean H d e S q T f x|≤1 := by
  induction H generalizing d e with
  | zero => exact PrescribedTree.treeMean_bound .leaf T hf
  | succ H ih =>
    cases e with
    | zero => exact PrescribedTree.treeMean_bound _ T hf
    | succ e => exact ih (d+1) e (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

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

lemma conditionalScheduledProduct_bound {ι : Type*} [Fintype ι]
    (H d e : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (x : FinitePath Ω H) (i : Fin N) : |conditionalScheduledProduct H d e C q T f x i|≤1 := by
  unfold conditionalScheduledProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ =>
    conditionalScheduledMean_bound H d e (C j) (q j) T (fun y => f y i) (fun y => hf y i) x)

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
-- module Solutions.OAIQ041_DS.DilutedSpin_ConditionalSpatialContinuity
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

noncomputable local instance instDecidable_1_r33125b_1 (p : Prop) : Decidable p := Classical.propDecidable p
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
-- module Solutions.OAIQ041_DS.DilutedSpin_DepthChildMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.depthChildMomentDecidable
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {L : ℕ} [NeZero L]

lemma average_nonneg (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) : 0≤average D F := by
  apply FiniteLaw.expect_nonneg
  intro q
  split_ifs
  · exact hF q
  · exact le_rfl

lemma average_mono (D : (α → Fin L) → Prop) (F G : (α → Fin L) → ℝ)
    (h : ∀ q, D q → F q≤G q) : average D F≤average D G := by
  apply FiniteLaw.expect_mono
  intro q
  split_ifs with hd
  · exact h q hd
  · exact le_rfl

lemma average_const_mul (D : (α → Fin L) → Prop) (c : ℝ) (F : (α → Fin L) → ℝ) :
    average D (fun q => c*F q)= c*average D F := by
  unfold average
  rw [← FiniteLaw.expect_mul_left]
  apply FiniteLaw.expect_congr
  intro q
  split_ifs <;> simp

lemma average_sqrt_le (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) : average D (fun q => Real.sqrt (F q))≤Real.sqrt (average D F) := by
  have h := FiniteLaw.expect_sqrt_le (depthLaw α L) (fun q => if D q then F q else 0)
    (fun q => by split_ifs; exact hF q; exact le_rfl)
  have he : (fun q => Real.sqrt (if D q then F q else 0)) =
      (fun q => if D q then Real.sqrt (F q) else 0) := by
    funext q
    split_ifs <;> simp
  rw [he] at h
  exact h

lemma fiber_sqrt_bound (e : β → α) (he : Function.Injective e)
    (τ : β → Equiv.Perm (Fin L)) (D : (α → Fin L) → Prop) (E : (β → Fin L) → Prop)
    (hDE : ∀ q, D q → E (coordinateProjection e τ q)) (F : (β → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) :
    average D (fun q => Real.sqrt (F (coordinateProjection e τ q)))≤
      Real.sqrt (average E F) :=
  (fiber_bound e he τ D E hDE (fun q => Real.sqrt (F q)) (fun _ => Real.sqrt_nonneg _)).trans
    (average_sqrt_le E F hF)

/-- The exact nested square roots occurring in the physical root multileaf
estimate pass through the normalized depth fibers. Every child uses its own
retained coordinates; unused coordinates have mass one. -/
theorem fiber_child_moment_bound {ι : Type} [Fintype ι]
    {β : ι → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    (c : ℝ) (hc : 0 ≤ c) (e : (j : ι) → β j → α) (he : ∀ j, Function.Injective (e j))
    (τ : (j : ι) → β j → Equiv.Perm (Fin L))
    (D : (α → Fin L) → Prop) (E : (j : ι) → (β j → Fin L) → Prop)
    (hDE : ∀ j q, D q → E j (coordinateProjection (e j) (τ j) q))
    (F : (j : ι) → (β j → Fin L) → ℝ) (hF : ∀ j q, 0≤F j q) :
    average D (fun q => Real.sqrt (c*∑ j, Real.sqrt (F j (coordinateProjection (e j) (τ j) q)))) ≤
      Real.sqrt (c*∑ j, Real.sqrt (average (E j) (F j))) := by
  apply (average_sqrt_le D _ (fun q => mul_nonneg hc
    (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)))).trans
  apply Real.sqrt_le_sqrt
  rw [average_const_mul,average_sum]
  apply mul_le_mul_of_nonneg_left _ hc
  apply Finset.sum_le_sum
  intro j _
  exact fiber_sqrt_bound (e j) (he j) (τ j) D (E j) (hDE j) (F j) (hF j)

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_EarliestChildDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance earliestChildDepthPropDecidable_r33125b_1 (proposition : Prop) :
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalPairConnection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
lemma readVector_bound (read : Site N → FinitePath Ω (L+1) → Spin) (x) (i) :
    |readVector read x i| ≤ 1 := by simp only [readVector,abs_spin,le_refl]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullCubeConditionalContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

end DilutedSpinGlass.UniversalDictionary
end

end

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
-- module Solutions.OAIQ041_DS.DilutedSpin_ProjectionShiftError
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
noncomputable local instance projectionShiftErrorPropDecidable_r33125b_1 (proposition : Prop) :
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
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProjectionShiftError
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
theorem root_averaged_projectionShiftError_le {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
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

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeightTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass

namespace PrescribedTree
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n m N : ℕ}

lemma leafHeightCast_bijective (h : n=m) (S : PrescribedTree n) :
    Function.Bijective (leafHeightCast h S) := by cases h; exact Function.bijective_id

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableProjector
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z]

omit [Fintype Ω] in
lemma measurable_leafProduct {n : ℕ} (S : PrescribedTree n)
    {g : Z → FinitePath Ω n → ℝ} (hg : ∀ y, Measurable (fun z => g z y))
    (a : S.Sample Ω) : Measurable (fun z => leafProduct S (g z) a) := by
  simp_rw [leafProduct_eq_prod]
  exact Finset.measurable_prod _ (fun b _ => hg _)

lemma measurable_treeMean_tilt {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin n → ℝ) {f g : Z → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y)) :
    Measurable (fun z => treeMean S (KernelTower.tilt n T m (f z)) (g z)) := by
  simp_rw [treeMean_eq_expect]
  exact measurable_tilt_sample_expect S T m hf (measurable_leafProduct S hg)

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma measurable_conditionalScheduledMean_tilt (H d e : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f g : Z → FinitePath Ω H → ℝ} (hf : ∀ y, Measurable (fun z => f z y))
    (hg : ∀ y, Measurable (fun z => g z y)) (x : FinitePath Ω H) :
    Measurable (fun z => conditionalScheduledMean H d e S q (KernelTower.tilt H T m (f z)) (g z) x) := by
  induction H generalizing d e with
  | zero => exact hg ()
  | succ H ih =>
    cases e with
    | zero => exact PrescribedTree.measurable_treeMean_tilt _ T m hf hg
    | succ e =>
        exact ih (d+1) e (T.2 x.1) (fun j => m j.succ)
          (fun y => hf (x.1,y)) (fun y => hg (x.1,y)) x.2

lemma measurable_conditionalScheduledProduct_tilt {ι : Type} [Fintype ι]
    (H d e : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f : Z → FinitePath Ω H → ℝ} {g : Z → FinitePath Ω H → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y i, Measurable (fun z => g z y i))
    (x : FinitePath Ω H) (i : Fin N) :
    Measurable (fun z => conditionalScheduledProduct H d e C q (KernelTower.tilt H T m (f z)) (g z) x i) := by
  unfold conditionalScheduledProduct
  exact Finset.measurable_prod _ (fun j _ =>
    measurable_conditionalScheduledMean_tilt H d e (C j) (q j) T m hf (fun y => hg y i) x)

lemma measurable_projectorChangeSq_tilt (H : ℕ) (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f : Z → FinitePath Ω H → ℝ} {X Y : Z → FinitePath Ω H → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i))
    (hY : ∀ y i, Measurable (fun z => Y z y i)) :
    Measurable (fun z => projectorChangeSq (KernelTower.tilt H T m (f z)) (X z) (Y z)) := by
  apply KernelTower.measurable_path_expect H T m hf
  intro y
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => ((hX y i).sub (hY y i)).pow_const 2)

lemma projectorChangeSq_le_four {H : ℕ} (T : KernelTower Ω H)
    (X Y : FinitePath Ω H → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) (hY : ∀ y i, |Y y i|≤1) : projectorChangeSq T X Y≤4 := by
  apply ((KernelTower.law H T).expect_mono (fun y => show FiniteLaw.spatialSq (fun i => X y i-Y y i)≤4 from ?_)).trans_eq
    ((KernelTower.law H T).expect_const 4)
  by_cases hN : N=0
  · simp [FiniteLaw.spatialSq,hN]
  · unfold FiniteLaw.spatialSq
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
    calc
      _ ≤ ∑ _ : Fin N, (4:ℝ) := Finset.sum_le_sum (fun i _ => by
        have hx := abs_le.mp (hX y i)
        have hy := abs_le.mp (hY y i)
        nlinarith [sq_nonneg (2-(X y i-Y y i)),sq_nonneg (2+(X y i-Y y i)),
          mul_nonneg (show 0≤2-(X y i-Y y i) by linarith) (show 0≤2+(X y i-Y y i) by linarith)])
      _ = _ := by simp; ring

variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] {L : ℕ} [NeZero L]

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma measurable_projectionShiftError_tilt (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f : Z → FinitePath Ω L → ℝ} {g : Z → FinitePath Ω L → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y i, Measurable (fun z => g z y i))
    (Q : α → Fin L) :
    Measurable (fun z => projectionShiftError a C e (KernelTower.tilt L T m (f z)) (g z) Q) := by
  unfold projectionShiftError
  apply Measurable.const_mul
  apply Measurable.sqrt
  exact measurable_projectorChangeSq_tilt L T m hf
    (measurable_conditionalScheduledProduct_tilt L 0 _ C _ T m hf hg)
    (measurable_conditionalScheduledProduct_tilt L 0 _ C _ T m hf hg)

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_le_four (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ)
    (hf : ∀ y i, |f y i|≤1) (Q : α → Fin L) : projectionShiftError a C e T f Q≤4 := by
  have h := projectorChangeSq_le_four T _ _
    (conditionalScheduledProduct_bound L 0 ((Q a).val+1) C
      (fun j v => (Q (e j v)).val+1) T f hf)
    (conditionalScheduledProduct_bound L 0 (Q a).val C
      (fun j v => (Q (e j v)).val) T f hf)
  have h' := Real.sqrt_le_sqrt h
  norm_num at h'
  unfold projectionShiftError
  linarith

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootShiftIntegrability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ReducedTopology
open scoped BigOperators
attribute [local irreducible] ReducedTopology.projectionShiftError
variable {Ω I X Y α ι : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype α] [DecidableEq α] [Fintype ι]
    {L M N : ℕ} [NeZero L]

variable (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (P : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
omit [Fintype α] [DecidableEq α] [NeZero L] in
/-- The exact single-copy shift error is measurable at the physical root,
including all Poisson counts and its countable variable marker alphabet. -/
lemma measurable_root_projectionShiftError (Q : α → Fin L) :
    Measurable (fun z : FullRootState Y X I M =>
      projectionShiftError a C e (rootTower T P m base old z) (rootVector V z) Q) := by
  change Measurable (packRoot (fun h k x n y =>
    projectionShiftError a C e
      (KernelTower.tilt L (tower (rootArray n y) L T P) m
        (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) L w)) Q))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_projectionShiftError_tilt a C e (tower (rootArray n y) L T P) m ?_ ?_ Q
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ _ => measurable_const

include hb in
omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma integrable_root_projectionShiftError (μ : Measure (FullRootState Y X I M))
    [IsFiniteMeasure μ] (hV : ∀ y i, |V y i|≤1) (Q : α → Fin L) :
    Integrable (fun z : FullRootState Y X I M =>
      projectionShiftError a C e (rootTower T P m base old z) (rootVector V z) Q) μ := by
  apply Integrable.of_bound (measurable_root_projectionShiftError a C e T P m base old V hb Q).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (projectionShiftError_nonneg a C e _ _ Q)]
  exact projectionShiftError_le_four a C e _ _ (fun y i => hV _ i) Q

include hb in
 
theorem physical_root_shift_average (μ : Measure (FullRootState Y X I M))
    [IsProbabilityMeasure μ] (hV : ∀ y i, |V y i|≤1)
    (he : ∀ j, Function.Injective (e j)) (η : ℝ) (hlarge : 1<η*(L:ℝ))
    (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, ReducedTopology.Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v))) :
    DepthAverage.average D (fun Q => ∫ z,
      projectionShiftError a C e (rootTower T P m base old z) (rootVector V z) Q ∂μ) ≤
      Real.sqrt (8*((Fintype.card ι:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (ReducedTopology.vertexArity (C j) v:ℝ)^2))+
          (Fintype.card ι:ℝ)^2)/(L:ℝ)) := by
  apply root_averaged_projectionShiftError_le μ
    (rootAlphabet (Ω := Ω) (A := A)) a C e he η hlarge D hD
    (rootTower T P m base old) (rootVector V) (fun z y i => hV _ i)
  exact integrable_root_projectionShiftError a C e T P m base old V hb μ hV

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

lemma scheduledShapeEnergy_nonneg (d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) :
    0 ≤ scheduledShapeEnergy L d S q T f := by
  unfold scheduledShapeEnergy
  split_ifs
  · exact shapeEnergyAt_nonneg _ _ _ _
  · exact le_rfl

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledRootMultileaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory DepthAverage
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.scheduledRootMultileafDecidableEq
noncomputable local instance scheduledRootMultileafDecidable_r33125b_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma childCoordinates_injective {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) : Function.Injective (childCoordinates (hk := hk) (C := C) j) := by
  intro x y h
  cases x <;> cases y <;> simp_all [childCoordinates]

lemma admissible_shift_same_upper (S : ReducedTopology) (q : S.Vertex → ℕ)
    {lo L : ℕ} (ha : Admissible S q lo L) (hr : ∀ v, q v+1<L) :
    Admissible S (fun v => q v+1) (lo+1) L := by
  induction S generalizing lo with
  | leaf => trivial
  | node k hk C ih =>
    refine ⟨by change lo+1 ≤ q none+1; have hh := ha.1; omega,hr none,?_⟩
    intro j
    exact ih j _ (ha.2.2 j) (fun v => hr (some ⟨j,v⟩))

/-- Both the old and all-coordinates-delayed proper child lie in the SAME
admissible regular domain. Rotation is genuinely +1 here: no wraparound is
silently admitted at the terminal level. -/
theorem regular_child_projection {L : ℕ} [NeZero L] {η : ℝ}
    (hη : 0<η) (hlarge : 4<η*(L:ℝ))
    {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) (s : Bool) {Q : Option (ReducedTopology.node k hk C).Vertex → Fin L}
    (hQ : regularShapeDomain (.node k hk C) L η Q) :
    regularShapeDomain (C j) L (η/2)
      (coordinateProjection (childCoordinates (hk := hk) j) (fun _ => shiftPerm s) Q) := by
  refine ⟨regular_shift_restrict hη hlarge _ (childCoordinates_injective j) (fun _ => s) hQ.1,?_⟩
  have ha := hQ.2.2.2 j
  cases s with
  | false => simpa only [coordinateProjection,shiftPerm,Bool.false_eq_true,ite_false,
      Equiv.refl_apply,childCoordinates] using ha
  | true =>
    have hroom : ∀ v : Option (ReducedTopology.node k hk C).Vertex, (Q v).val+1<L :=
      regular_room (by linarith : 1<η*(L:ℝ)) hQ.1
    have hh := admissible_shift_same_upper (C j) _ ha
      (fun v => hroom (some (some ⟨j,v⟩)))
    simpa only [coordinateProjection,shiftPerm,ite_true,childCoordinates,
      rotate_val_of_room _ (hroom _)] using hh

 
theorem regular_scheduled_child_moment {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)] {L N : ℕ} [NeZero L]
    (T : (z : Z) → KernelTower (Ω z) L)
    (f : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L:ℝ))
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) (s : Bool) :
    let F := fun (j : Fin k) (q : Option (C j).Vertex → Fin L) =>
      ∫ z, scheduledShapeEnergy L (q none).val (C j) (fun v => (q (some v)).val) (T z) (f z) ∂μ
    average (regularShapeDomain (.node k hk C) L η)
      (fun Q => Real.sqrt ((k:ℝ)*∑ j, Real.sqrt
        (F j (coordinateProjection (childCoordinates (hk := hk) j) (fun _ => shiftPerm s) Q)))) ≤
      Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (average (regularShapeDomain (C j) L (η/2)) (F j))) := by
  dsimp only
  refine fiber_child_moment_bound (k:ℝ) (by positivity)
    (fun j => childCoordinates (hk := hk) j) (fun j => childCoordinates_injective j)
    (fun _ _ => shiftPerm s) (regularShapeDomain (.node k hk C) L η)
    (fun j => regularShapeDomain (C j) L (η/2)) ?_
    (fun j q => ∫ z, scheduledShapeEnergy L (q none).val (C j)
      (fun v => (q (some v)).val) (T z) (f z) ∂μ) ?_
  · intro j Q hQ
    exact regular_child_projection hη hlarge j s hQ
  · intro j q
    exact integral_nonneg (fun z => scheduledShapeEnergy_nonneg _ _ _ _ _)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShiftedFrameGeometry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable local instance shiftedFrameGeometryPropDecidable_r33125b_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma branchingCount_stem (S : PrescribedTree n) (r : ℕ) (P : ℕ → Prop) :
    branchingCount (stem S r) P=branchingCount S (fun u => P (u+r)) := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
    change branchingCount (unary (stem S r)) P=_
    rw [branchingCount_unary,ih]
    simp only [Nat.add_assoc]

lemma mem_shiftedPrefixDepths (S : PrescribedTree n) (d u : ℕ) :
    u+d ∈ shiftedPrefixDepths S d ↔ u ∈ shiftedTwinDepths S := by
  classical
  simp [shiftedPrefixDepths]

theorem shifted_prefix_total_count (S : PrescribedTree n) (d : ℕ) :
    branchingCount (stem (doubled (unary S)) d) (fun _ => True)=
      branchingCount (stem (doubled (unary S)) d) (· ∈ shiftedPrefixDepths S d)+1 := by
  rw [branchingCount_stem,branchingCount_stem]
  simpa only [mem_shiftedPrefixDepths] using shifted_twin_total_count S

lemma branchRegular_unary {n : ℕ} (S : PrescribedTree n) (m : Fin (n+2) → ℝ) (η : ℝ) :
    BranchRegular (unary S) m η ↔ BranchRegular S (fun j => m j.succ) η := by
  simp only [unary,BranchRegular]
  simp

lemma branchRegular_grid_stem (S : PrescribedTree n) (r d L : ℕ) (η : ℝ) :
    BranchRegular (stem S r) (grid (n+r) d L) η ↔
      BranchRegular S (grid n (d+r) L) η := by
  induction r generalizing d with
  | zero => simp only [Nat.add_zero]; rfl
  | succ r ih =>
    change BranchRegular (unary (stem S r)) (grid (n+r+1) d L) η ↔ _
    rw [branchRegular_unary]
    have he : (fun j : Fin (n+r+1) => grid (n+r+1) d L j.succ)=grid (n+r) (d+1) L := by
      funext j
      simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
    rw [he,ih]
    rw [show d+1+r=d+(r+1) by omega]

/-- All higher-degree factors below a regularly interior evaluation depth
are uniformly positive; no regularity of a union of shapes is needed. -/
lemma branchRegular_grid_of_lower (S : PrescribedTree n) (d L : ℕ) (η : ℝ)
    (h : η≤(d:ℝ)/(L:ℝ)) : BranchRegular S (grid n d L) η := by
  induction S generalizing d with
  | leaf => trivial
  | @node n k C ih =>
    have h' : η≤((d+1:ℕ):ℝ)/(L:ℝ) := h.trans (by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
      exact_mod_cast Nat.le_succ d)
    constructor
    · intro _
      simpa [grid] using h'
    · intro i
      have he : (fun j : Fin (n+1) => grid (n+1) d L j.succ)=grid n (d+1) L := by
        funext j
        simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
      rw [he]
      exact ih i (d+1) h'

lemma branchRegular_shifted_frame (S : PrescribedTree n) (r d L : ℕ) (η : ℝ)
    (he : η≤((d+r+2:ℕ):ℝ)/(L:ℝ)) :
    BranchRegular (stem (doubled (unary (stem S r))) d)
      (grid (n+r+1+1+d) 0 L) η := by
  rw [branchRegular_grid_stem]
  simp only [Nat.zero_add,doubled,BranchRegular]
  refine ⟨by norm_num,?_⟩
  intro i
  have hgrid : (fun j : Fin (n+r+1+1) => grid (n+r+1+1) d L j.succ)=grid (n+r+1) (d+1) L := by
    funext j
    simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
  rw [hgrid,branchRegular_unary]
  have hgrid' : (fun j : Fin (n+r+1) => grid (n+r+1) (d+1) L j.succ)=grid (n+r) (d+2) L := by
    funext j
    simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
  rw [hgrid',branchRegular_grid_stem]
  apply branchRegular_grid_of_lower
  simpa only [show d+2+r=d+r+2 by omega] using he

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledFrameGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n m : ℕ}

lemma branchRegular_heightCast (h : n=m) (S : PrescribedTree n) (d L : ℕ) (η : ℝ) :
    BranchRegular (heightCast h S) (grid m d L) η ↔ BranchRegular S (grid n d L) η := by
  cases h; rfl

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- All target branches except the protected separation vertex are charged. -/
theorem scheduled_frame_target_total (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    branchingCount Target (fun _ => True)=
      branchingCount Target (· ∈ shiftedPrefixDepths (stem Base r) d)+1 := by
  dsimp only
  simp only [branchingCount_heightCast]
  have he : (PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j)
      (fun v => (Q (e j v)).val+1))) =
      PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val)) := by
    congr 1
    funext j
    rw [show r+1+1+d+1=(r+1+d+1)+1 by omega,realize_translate]
  rw [he]
  change branchingCount (stem (doubled (unary (stem _ r))) d) _=_
  exact shifted_prefix_total_count _ d

omit [Fintype α] [DecidableEq α] in
/-- Higher-degree target factors are uniformly interior at every regular
first split. No premise is imposed on an overlay of the two shapes. -/
theorem scheduled_frame_target_regular (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (η : ℝ)
    (heval : η≤((d+r+2:ℕ):ℝ)/((H+1+1+r+1+d:ℕ):ℝ)) :
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    BranchRegular Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) η := by
  dsimp only
  rw [branchRegular_heightCast]
  change BranchRegular (stem (doubled (unary (stem _ r))) d) _ _
  exact branchRegular_shifted_frame _ r d _ η heval

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TwoPointLabeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass

/-- Finite labeling can pin both protected leaves without changing the full
leaf set; this is not an assumed identification of the two tree experiments. -/
lemma exists_equiv_two_points {α β : Type} [Fintype α] [Fintype β]
    (hcard : Fintype.card α=Fintype.card β) (a b : α) (c d : β)
    (hab : a≠b) (hcd : c≠d) : ∃ e : α ≃ β, e a=c ∧ e b=d := by
  classical
  let e₀ := Fintype.equivOfCardEq hcard
  let e₁ := e₀.trans (Equiv.swap (e₀ a) c)
  have ha : e₁ a=c := by simp [e₁]
  have hb : e₁ b≠c := by rw [← ha]; exact fun h => hab (e₁.injective h).symm
  refine ⟨e₁.trans (Equiv.swap (e₁ b) d),?_,?_⟩
  · simp only [Equiv.trans_apply,ha]
    exact Equiv.swap_apply_of_ne_of_ne hb.symm hcd
  · simp

namespace PrescribedTree

/-- Every split frame has a canonical Option/Fin dictionary labeling with
`none` and the FIRST inserted label at the protected corresponding twin leaves. -/
lemma splitFrame_canonical_labeling {n : ℕ} (S : PrescribedTree n) (r d t : ℕ)
    (b : S.Leaf) (hcard : Fintype.card (splitFrame S r d).Leaf=t+2) :
    ∃ q : Option (Fin (t+1)) ≃ (splitFrame S r d).Leaf,
      q none=splitFrameLeaf S r d 0 b ∧
      q (some (Fin.last t))=splitFrameLeaf S r d 1 b := by
  apply exists_equiv_two_points
  · simpa only [Fintype.card_option,Fintype.card_fin] using hcard.symm
  · simp
  · intro h
    have he := splitFrame_split S r d b
    rw [h,splitDepth_self] at he
    omega

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularPhysicalShift
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology

noncomputable local instance instDecidableEq_r33125b_1 (β : Type) : DecidableEq β := Classical.decEq β
lemma childBranchCoordinates_injective {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) : Function.Injective (childBranchCoordinates (hk := hk) (C := C) j) := by
  intro x y h
  have hh := congrArg Subtype.val h
  simpa only [childBranchCoordinates,Option.some.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh

lemma regular_child_branches {L : ℕ} [NeZero L] {η : ℝ}
    {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) {Q : Option (ReducedTopology.node k hk C).Vertex → Fin L}
    (hQ : DepthAverage.Regular η Q) :
    DepthAverage.Regular η (fun v => Q ((childBranchCoordinates (hk := hk) (C := C) j v).val)) := by
  constructor
  · intro v
    exact hQ.1 _
  · intro v w hvw
    exact hQ.2 _ _ (fun h => hvw (childBranchCoordinates_injective j (Subtype.ext h)))

end DilutedSpinGlass.ReducedTopology
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}
attribute [local irreducible] projectionShiftError

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.instDecidableEq_solutions
/-- The uniform h_N bound on the FULL actual regular/admissible parent domain,
with the literal physical root and exactly its proper-child embeddings. This
has no geometry or ordinary-integrability hypothesis left to discharge. -/
theorem regular_physical_shift_average (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (η : ℝ) (hlarge : 1<η*(L+1:ℕ)) :
    let μ := fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N)
    let K := rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    let f := rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v))
      (I := Labels L (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N)
    DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η)
      (fun Q => ∫ z, projectionShiftError (some none) C
        (fun j => childBranchCoordinates (hk := hk) j) (K z) (f z) Q ∂μ) ≤
      Real.sqrt (8*((k:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(k:ℝ)^2)/(L+1:ℕ)) := by
  dsimp only
  have hh := physical_root_shift_average (some none) C
    (fun j => childBranchCoordinates (hk := hk) j)
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (readVector (fun v x => readSpin (KernelTower.terminalState L x) v))
    (measurable_physicalBase M θB hB N)
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (readVector_bound _) (fun j => childBranchCoordinates_injective j)
    η hlarge (regularShapeDomain (.node k hk C) (L+1) η) (by
      intro Q hQ j
      exact ⟨hQ.2.2.2 j, regular_child_branches j hQ.1⟩)
  simpa only [Fintype.card_fin] using hh

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalScheduledStep
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}


attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.physicalScheduledStepDecidableEq
lemma physicalScheduledEnergy_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) :
    0 ≤ physicalScheduledEnergy M θB hB N L u S Q :=
  integral_nonneg (fun _ => scheduledShapeEnergy_nonneg _ _ _ _ _)


theorem physical_scheduled_child_moment (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ))
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) (s : Bool) :
    DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η)
      (fun Q => Real.sqrt ((k:ℝ)*∑ j, Real.sqrt
        (physicalScheduledEnergy M θB hB N L u (C j)
          (DepthAverage.coordinateProjection (childCoordinates (hk := hk) j)
            (fun _ => DepthAverage.shiftPerm s) Q)))) ≤
      Real.sqrt ((k:ℝ)*∑ j, Real.sqrt
        (DepthAverage.average (regularShapeDomain (C j) (L+1) (η/2))
          (physicalScheduledEnergy M θB hB N L u (C j)))) := by
  exact regular_scheduled_child_moment
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1))
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))
    hη hlarge k hk C s

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularFrameExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage

noncomputable local instance regularFrameExtractionDecidableEq_r33125b_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma admissible_replace_upper (S : ReducedTopology) (q : S.Vertex → ℕ)
    {lo hi hi' : ℕ} (ha : Admissible S q lo hi) (hr : ∀ v, q v<hi') :
    Admissible S q lo hi' := by
  induction S generalizing lo with
  | leaf => trivial
  | node k hk C ih =>
    exact ⟨ha.1,hr none,fun j => ih j _ (ha.2.2 j) (fun v => hr (some ⟨j,v⟩))⟩

/-- Every assignment in the actual regular/admissible parent domain is one
of the literal frames of physical_grid_scheduled_step. The extraction keeps
the complete terminal horizon, evaluation level and first branching level;
it loses neither endpoint cases nor further child branching coordinates. -/
theorem regular_node_frame {L : ℕ} [NeZero L] {η : ℝ} (hη : 0<η)
    (hlarge : 1<η*(L:ℝ)) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin L)
    (hQ : regularShapeDomain (.node k hk C) L η Q) :
    ∃ H r d : ℕ, L=H+1+1+r+1+(d+1) ∧ (Q none).val=d+1 ∧
      (Q (some none)).val=r+1+(d+1) ∧
      ∀ j, Admissible (C j) (fun v => (Q (some (some ⟨j,v⟩))).val)
        (r+1+(d+1)+1) (r+1+(d+1)+1+H) := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hdpos : 0<(Q none).val := by
    have hh := (lt_div_iff₀ hL).mp (hQ.1.1 none).1
    have hh' : (0:ℝ)<((Q none).val:ℝ) := (mul_pos hη hL).trans hh
    exact_mod_cast hh'
  have heval : (Q none).val+1≤(Q (some none)).val := hQ.2.1
  have hroom := regular_room hlarge hQ.1
  let d := (Q none).val-1
  let r := (Q (some none)).val-(Q none).val-1
  let H := L-(Q (some none)).val-2
  have hd : (Q none).val=d+1 := by dsimp [d]; omega
  have hr : (Q (some none)).val=r+1+(d+1) := by dsimp [r,d]; omega
  have hH : L=H+1+1+r+1+(d+1) := by
    have hh := hroom (some none)
    dsimp [H,r,d]
    omega
  refine ⟨H,r,d,hH,hd,hr,?_⟩
  intro j
  have ha := admissible_replace_upper (C j) _ (hQ.2.2.2 j)
    (hi' := r+1+(d+1)+1+H) (by
      intro v
      have hh := hroom (some (some ⟨j,v⟩))
      change (Q (some (some ⟨j,v⟩))).val < r+1+(d+1)+1+H
      omega)
  simpa only [hr] using ha

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledEnergyBound
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

lemma centered_square_le_one (P : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ x, |f x|≤1) :
    P.expect (fun x => (f x-P.expect f)^2)≤1 := by
  have hs : P.expect (fun x => f x^2)≤1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        simpa using sq_le_sq.mpr (show |f x|≤|(1:ℝ)| by simpa using hf x))
      _ = _ := P.expect_const 1
  have he : P.expect (fun x => (f x-P.expect f)^2)=P.expect (fun x => f x^2)-(P.expect f)^2 := by
    calc
      _ = P.expect (fun x => f x^2-2*P.expect f*f x+(P.expect f)^2) := P.expect_congr (fun x => by ring)
      _ = _ := by simp; ring
  rw [he]
  nlinarith [sq_nonneg (P.expect f)]

lemma covariance_sq_le_one (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) : (P.covariance f g)^2≤1 := by
  rw [P.covariance_centered]
  exact (P.expect_mul_sq_le _ _).trans (by
    have hh := mul_le_mul (P.centered_square_le_one f hf) (P.centered_square_le_one g hg)
      (P.expect_nonneg (fun x => sq_nonneg (g x-P.expect g))) zero_le_one
    simpa only [one_mul] using hh)

lemma covarianceEnergy_le_one {N : ℕ} (P : FiniteLaw Ω) (X : Ω → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) : P.covarianceEnergy X≤1 := by
  by_cases hN : N=0
  · simp [covarianceEnergy,hN]
  · have hpos : 0<(N:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
    unfold covarianceEnergy
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, (1:ℝ) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact P.covariance_sq_le_one _ _ (fun x => hX x i) (fun x => hX x j)
      _ = _ := by simp; ring

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma shapeEnergyAt_le_one (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (X : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : shapeEnergyAt C d T X≤1 := by
  induction d with
  | zero =>
      unfold shapeEnergyAt childEnergy
      apply FiniteLaw.covarianceEnergy_le_one
      intro a i
      exact leafProduct_bound C (fun y => hX (a.1,y) i) a.2
  | succ d ih =>
      exact (T.1.expect_mono (fun a => ih (T.2 a) (fun y => X (a,y))
        (fun y i => hX (a,y) i))).trans_eq (T.1.expect_const 1)

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

lemma scheduledShapeEnergy_le_one (d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω L) (X : FinitePath Ω L → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : scheduledShapeEnergy L d S q T X≤1 := by
  unfold scheduledShapeEnergy
  split_ifs
  · exact shapeEnergyAt_le_one _ _ _ _ (fun _ index => hX _ index)
  · exact zero_le_one

end DilutedSpinGlass.ReducedTopology
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}

noncomputable local instance scheduledEnergyBoundDecidableEq_r33125b_1 (type : Type) :
    DecidableEq type := Classical.decEq type
/-- Unit bound for the actual physical covariance, including N=0, leaves,
inadmissible schedules and the countable variable-alphabet root. -/
lemma physicalScheduledEnergy_le_one (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) :
    physicalScheduledEnergy M θB hB N L u S Q≤1 := by
  unfold physicalScheduledEnergy
  calc
    _ ≤ ∫ _, (1:ℝ) ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
        (markLaw (weights L) N) (M.alpha*N) (scoreRate N) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => scheduledShapeEnergy_nonneg _ _ _ _ _)
      · exact integrable_const _
      · exact Filter.Eventually.of_forall (fun _ => scheduledShapeEnergy_le_one _ _ _ _ _
          (fun _ _ => readVector_bound _ _ _))
    _ = 1 := by simp

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledProtectedLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

lemma leaves_stem {n : ℕ} (S : PrescribedTree n) (r : ℕ) :
    leaves (stem S r)=leaves S := by
  induction r with
  | zero => rfl
  | succ r ih => rw [stem,leaves_unary,ih]

lemma leaves_doubled {n : ℕ} (S : PrescribedTree n) :
    leaves (doubled S)=2*leaves S := by
  change (∑ _ : Fin 2, leaves S)=2*leaves S
  simp [Nat.two_mul]

lemma leaves_splitFrame {n : ℕ} (S : PrescribedTree n) (r d : ℕ) :
    leaves (splitFrame S r d)=2*leaves S := by
  rw [splitFrame,leaves_stem,leaves_doubled,leaves_stem]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

/-- The shifted children retain exactly their topology leaves. In particular
one fixed dictionary arity works for every admissible depth assignment. -/
lemma delayed_node_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize H (lo+1) (C j)
      (fun v => q j v+1))) = Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize H (lo+1) (C j) (fun v => q j v+1))) =
    Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [realize_translate H lo 1,realize_leaves H lo (C j) (q j) (had j)])

/-- Actual assignment-dependent protected labeling for the genuinely delayed
multileaf target. The dictionary size depends only on the reduced topology,
not the grid horizon or any of its branching-coordinate assignments. -/
theorem delayed_node_protected_labeling (H lo r d : ℕ) (k : ℕ+)
    (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    let S := PrescribedTree.node k (fun j => realize H (lo+1) (C j)
      (fun v => q j v+1))
    let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
    ∃ (b : S.Leaf) (e : Option (Fin (t+1)) ≃ (splitFrame S r d).Leaf),
      e none=splitFrameLeaf S r d 0 b ∧
      e (some (Fin.last t))=splitFrameLeaf S r d 1 b := by
  dsimp only
  let S := PrescribedTree.node k (fun j => realize H (lo+1) (C j)
    (fun v => q j v+1))
  have hcard := delayed_node_leaves H lo k hk C q had
  have hpos := leaves_pos S
  have hc : Fintype.card (splitFrame S r d).Leaf =
      2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+2 := by
    rw [card_leaf,leaves_splitFrame]
    change leaves S = _ at hcard
    rw [hcard]
    omega
  obtain ⟨b⟩ := leaf_nonempty S
  obtain ⟨e,he₀,he₁⟩ := splitFrame_canonical_labeling S r d
    (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2) b hc
  exact ⟨b,e,he₀,he₁⟩

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledRelativeCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}

lemma partialKappa_ratio_bijective (T : PrescribedTree n) (q : I → T.Leaf)
    (hq : Function.Bijective q) (m : Fin (n+1) → ℝ) (u v : I) :
    partialKappa T m (Finset.univ.image q)/partialKappa T m ((insert v ({u}:Finset I)).image q)=
      partialKappa T m Finset.univ/partialKappa T m {q v,q u} := by
  classical
  rw [Finset.image_univ_of_surjective hq.2]
  simp only [Finset.image_insert,Finset.image_singleton]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_le_const (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    {B : ℝ} (hB : 0≤B) (hF : ∀ q, D q → F q≤B) : average D F≤B := by
  calc
    _ ≤ (depthLaw α L).expect (fun _ => B) := by
      apply FiniteLaw.expect_mono
      intro q
      split_ifs with hd
      · exact hF q hd
      · exact hB
    _ = _ := FiniteLaw.expect_const _ _

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TopologyChargeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- Exact leaf budget, counting vertices with multiplicity and not merely
branching depth values. Unary grid levels consume no budget. -/
lemma branch_budget {n : ℕ} (S : PrescribedTree n) :
    branchingCount S (fun _ => True)+branchExcess S+1=leaves S := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    have hs : (∑ i, branchingCount (C i) (fun _ => True))+
        (∑ i, branchExcess (C i))+(k:ℕ)=∑ i, leaves (C i) := by
      calc
        _ = ∑ i, (branchingCount (C i) (fun _ => True)+branchExcess (C i)+1) := by
          simp [Finset.sum_add_distrib]
        _ = _ := Finset.sum_congr rfl (fun i _ => ih i)
    simp only [branchingCount,branchExcess,leaves,true_and]
    have hp : 0 < (k:ℕ) := k.property
    split <;> omega

lemma branchingDepths_card_le {n : ℕ} (S : PrescribedTree n) :
    (branchingDepths S).card≤branchingCount S (fun _ => True) := by
  classical
  rw [branchingCount_eq_vertexSum]
  simp only [and_true]
  calc
    _ ≤ (Finset.univ.filter (fun v : S.Internal => 1<vertexArity S v)).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_eq_sum_ones,Finset.sum_filter]

lemma shiftedPrefixDepths_card_le {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    (shiftedPrefixDepths S d).card≤leaves S := by
  calc
    _ ≤ (shiftedTwinDepths S).card := Finset.card_image_le
    _ ≤ (branchingDepths S).card := Finset.card_image_le
    _ ≤ branchingCount S (fun _ => True) := branchingDepths_card_le S
    _ ≤ leaves S := by have h := branch_budget S; omega

lemma chargeBound_le_pow {C D : ℝ} (hC : 0≤C) (hD : 0≤D) (k b : ℕ) :
    chargeBound C D k b≤(C+D)^k := by
  induction k generalizing b with
  | zero => simp only [chargeBound,pow_zero]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero =>
      simp only [chargeBound,pow_succ]
      calc
        _ ≤ C*(C+D)^k := mul_le_mul_of_nonneg_left (ih 0) hC
        _ ≤ _ := by nlinarith [pow_nonneg (add_nonneg hC hD) k]
    | succ b =>
      simp only [chargeBound,pow_succ]
      calc
        _ ≤ C*(C+D)^k+D*(C+D)^k := add_le_add
          (mul_le_mul_of_nonneg_left (ih _) hC) (mul_le_mul_of_nonneg_left (ih _) hD)
        _ = _ := by ring

/-- A topology-only constant for the genuine relative signed-history cost.
The grid size is absent. Its hypotheses are just leaf/depth counts, not a
covariance estimate or any desired limiting conclusion. -/
theorem shiftedCharge_relative_uniform {L : ℕ} (hL : 0<L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (k R : ℕ) (hQ : Q.card≤R)
    (hS : leaves S+k≤R) (hT : leaves T≤R)
    (a b : T.Leaf) (hab : a≠b) (η : ℝ) (hη : 0<η)
    (hr : BranchRegular T (grid L 0 L) η)
    (hb : branchingCount T (fun _ => True)=branchingCount T (· ∈ Q)+1) :
    shiftedCharge Q T S k /
      |partialKappa T (grid L 0 L) Finset.univ/partialKappa T (grid L 0 L) {b,a}| ≤
      (((2+(R:ℝ))*(R:ℝ))^k)/(min η 1)^R := by
  classical
  have hA := chargeBound_nonneg (C := 2*(leaves S+k:ℕ))
    (D := (Q.card:ℝ)*(leaves S+k:ℕ)) (by positivity) (by positivity) k
    (branchingCount T (· ∈ Q))
  have hp := chargeBound_le_pow (C := 2*(leaves S+k:ℕ))
    (D := (Q.card:ℝ)*(leaves S+k:ℕ)) (by positivity) (by positivity) k
    (branchingCount T (· ∈ Q))
  have hv : (2*(leaves S+k:ℕ)+(Q.card:ℝ)*(leaves S+k:ℕ))≤(2+(R:ℝ))*(R:ℝ) := by
    have hSr : ((leaves S+k:ℕ):ℝ)≤R := by exact_mod_cast hS
    have hQr : (Q.card:ℝ)≤R := by exact_mod_cast hQ
    nlinarith [mul_nonneg (sub_nonneg.mpr hSr) (by positivity : 0≤(R:ℝ)),
      mul_nonneg (sub_nonneg.mpr hQr) (show 0≤((leaves S+k:ℕ):ℝ) by positivity)]
  have hex : branchExcess T≤R := by have hh := branch_budget T; omega
  have hm : 0 < min η 1 := lt_min hη zero_lt_one
  have he : (min η 1)^R≤η^(branchExcess T) :=
    (pow_le_pow_of_le_one hm.le (min_le_right _ _) hex).trans
      (pow_le_pow_left₀ hm.le (min_le_left _ _) _)
  exact (shiftedCharge_relative_bound hL Q T S k a b hab η hη hr hb).trans
    (div_le_div₀ (by positivity) (hp.trans (pow_le_pow_left₀ (by positivity) hv _))
      (pow_pos hm _) he)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

lemma nodeChargeConstant_nonneg (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) {η : ℝ} (hη : 0<η) :
    0≤nodeChargeConstant k hk C η := by
  unfold nodeChargeConstant
  exact div_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (le_min hη.le zero_le_one) _)

lemma node_realize_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize H lo (C j) (q j))) =
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize H lo (C j) (q j))) = Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => realize_leaves H lo (C j) (q j) (had j))

lemma node_old_realize_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize (H+1) lo (C j) (q j))) =
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize (H+1) lo (C j) (q j))) = Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [realize_bottom H lo (C j) (q j) (had j),leaves_bottom,
    realize_leaves H lo (C j) (q j) (had j)]

variable {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]

omit [Fintype α] [DecidableEq α] in
/-- The actual frame charging cost is bounded only by the reduced topology
and the separation parameter. The canonical ratio and vertex multiplicities
are retained; no maximization over a grid-dependent majorant is used. -/
theorem node_frame_charge_uniform (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d))
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    {η : ℝ} (hη : 0<η)
    (heval : η≤((d+r+2:ℕ):ℝ)/((H+1+1+r+1+d:ℕ):ℝ)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let Old := PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    let S := splitFrame Old r d
    let B := shiftedPrefixDepths (stem Base r) d
    let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
    ∀ (q : I → Target.Leaf), Function.Bijective q → ∀ (u v : I), u≠v →
    shiftedCharge B Target S (t+1) /
      |partialKappa Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) (Finset.univ.image q)/
        partialKappa Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) ((insert v ({u}:Finset I)).image q)| ≤
      nodeChargeConstant k hk C η := by
  dsimp only
  intro q hq u v huv
  rw [partialKappa_ratio_bijective _ q hq]
  have hbase := node_realize_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  have hold := node_old_realize_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  have hnew := delayed_node_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  rw [show r+1+d+1+1=r+1+1+d+1 by omega] at hnew
  have hpos := leaf_card_pos (ReducedTopology.node k hk C)
  apply shiftedCharge_relative_uniform (by omega) _ _ _ _ (nodeHistoryBudget k hk C)
  · apply (shiftedPrefixDepths_card_le _ _).trans
    rw [leaves_stem,hbase]
    unfold nodeHistoryBudget
    omega
  · rw [leaves_splitFrame,hold]
    unfold nodeHistoryBudget
    omega
  · rw [leaves_heightCast,leaves_splitFrame,hnew]
    unfold nodeHistoryBudget
    omega
  · exact fun h => huv (hq.1 h)
  · exact hη
  · exact scheduled_frame_target_regular H r d k a C e Q η heval
  · exact scheduled_frame_target_total H r d k a C e Q

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeEstimates
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.regularNodeEstimatesDecidableEq
lemma physicalChildMass_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    0≤physicalChildMass M θB hB N L u k hk C s Q := by
  unfold physicalChildMass
  positivity

lemma physicalChildMass_le_square (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    physicalChildMass M θB hB N L u k hk C s Q≤(k:ℝ)^2 := by
  unfold physicalChildMass
  calc
    _ ≤ (k:ℝ)*∑ j : Fin k, (1:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      exact (Real.sqrt_le_sqrt (physicalScheduledEnergy_le_one M θB hB N L u (C j) _)).trans_eq
        Real.sqrt_one
    _ = _ := by simp; ring

lemma physicalChildMass_le_sqrt (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    physicalChildMass M θB hB N L u k hk C s Q ≤
      (k:ℝ)*Real.sqrt (physicalChildMass M θB hB N L u k hk C s Q) := by
  have h := Real.sqrt_le_sqrt (physicalChildMass_le_square M θB hB N L u k hk C s Q)
  rw [Real.sqrt_sq (by positivity : (0:ℝ)≤k)] at h
  have hm := mul_le_mul_of_nonneg_right h
    (Real.sqrt_nonneg (physicalChildMass M θB hB N L u k hk C s Q))
  simpa only [← sq,Real.sq_sqrt (physicalChildMass_nonneg M θB hB N L u k hk C s Q)] using hm


lemma physicalNodeShift_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    0≤physicalNodeShift M θB hB N L u k hk C Q :=
  integral_nonneg (fun _ => projectionShiftError_nonneg _ _ _ _ _ _)

lemma physicalNodeShift_average (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (η : ℝ) (hlarge : 1<η*(L+1:ℕ)) :
    DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η)
      (physicalNodeShift M θB hB N L u k hk C)≤Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)) :=
  regular_physical_shift_average M θB hB N L u k hk C η hlarge

lemma multileaf_scalar_bound {η c v δ err w w' h ch pa K P k : ℝ}
    (hc : η ≤ c) (hc1 : c≤1) (hv : 0≤v) (hw : 0≤w) (hh : 0≤h)
    (hch : ch≤K) (hpa : pa≤P) (hwk : w≤k*Real.sqrt w)
    (hstep : c*v≤2*(2*δ+err+(2*Real.sqrt w'+h)*ch+pa*(2*Real.sqrt w))+c*(16*w)) :
    η*v ≤ 4*δ+2*err+4*K*Real.sqrt w'+2*K*h+(4*P+16*k)*Real.sqrt w := by
  have h₁ := mul_le_mul_of_nonneg_left hch (by positivity : 0≤2*Real.sqrt w'+h)
  have h₂ := mul_le_mul_of_nonneg_right hpa (by positivity : 0≤2*Real.sqrt w)
  have h₃ := mul_le_mul_of_nonneg_right hc1 (by positivity : 0≤16*w)
  have h₄ := mul_le_mul_of_nonneg_left hwk (by norm_num : (0:ℝ)≤16)
  have h₅ := mul_le_mul_of_nonneg_right hc hv
  nlinarith only [hstep,h₁,h₂,h₃,h₄,h₅]

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeProducer
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.instDecidableEq_solutions_1
/-- On every regular admissible parent assignment there is one literal signed
matrix experiment. Its geometry is fixed before the physical size and probe
parameters are chosen, and its charging constants are independent of the grid.
This is the pointwise producer for the averaged decorrelation induction. -/
theorem regular_node_pointwise (M : Model p) (θB hB : ℝ) (L : ℕ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 1<η*(L+1:ℕ))
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1))
    (hQ : regularShapeDomain (.node k hk C) (L+1) η Q) :
    ∃ (S T : PrescribedTree (L+1)) (a : S.Leaf)
      (q : Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → T.Leaf)
      (J : ℝ), ∀ (N : ℕ) (u : Spec L × ℕ → ℝ),
    η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*(|physicalTreeMatrixCovariance (gridExponents L) S a M θB hB N u T q|/|J|) +
      4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
      2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
      (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q) := by
  obtain ⟨H,r,d,hL,hd,he,had⟩ := regular_node_frame hη hlarge k hk C Q hQ
  have hL' : L=H+1+1+r+1+d := by omega
  subst L
  let L₀ := H+1+1+r+1+d
  let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
  let OldNode := PrescribedTree.node k (fun j => realize (H+1) (r+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val))
  let NewNode := PrescribedTree.node k (fun j => realize H (r+1+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val+1))
  let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val))
  let S := splitFrame OldNode r (d+1)
  let RawTarget := splitFrame NewNode (r+1) (d+1)
  let ht := shiftedFrameHeight H r (d+1)
  let T := heightCast ht RawTarget
  obtain ⟨b⟩ := leaf_nonempty OldNode
  have hlabel := delayed_node_protected_labeling H (r+1+(d+1)+1) (r+1) (d+1) k hk C
    (fun j v => (Q (some (some ⟨j,v⟩))).val) had
  dsimp only at hlabel
  rw [show r+1+(d+1)+1+1=r+1+1+(d+1)+1 by omega] at hlabel
  obtain ⟨b',q₀,hq₀,hq₁⟩ := hlabel
  let q : Option (Fin (t+1)) → T.Leaf := fun i => leafHeightCast ht RawTarget (q₀ i)
  let a : S.Leaf := splitFrameLeaf OldNode r (d+1) 0 b
  let v : Option (Fin (t+1)) := some (Fin.last t)
  let m : Fin (L₀+2) → ℝ := Fin.cons 0 (gridExponents L₀)
  let J := partialKappa T m (Finset.univ.image q)/partialKappa T m ((insert v ({none}:Finset _)).image q)
  refine ⟨S,T,a,q,J,?_⟩
  intro N u
  have hstep := physical_grid_scheduled_step M θB hB N H r d u k hk (some none) C
    (fun j => childBranchCoordinates (hk := hk) j) Q he had hlarge hQ.1
    b b' q₀ q₀.bijective hq₀ hq₁
  dsimp only at hstep
  have hroom := DepthAverage.regular_room hlarge hQ.1
  have hrot (i : Option (ReducedTopology.node k hk C).Vertex) :
      ((finRotate (L₀+1)) (Q i)).val=(Q i).val+1 :=
    DepthAverage.rotate_val_of_room _ (hroom i)
  have hparent : (fun v => (Q (some v)).val) =
      rootSchedule (hk := hk) (r+1+(d+1)) (fun j v => (Q (some (some ⟨j,v⟩))).val) := by
    funext v
    cases v with
    | none => exact he
    | some v => rfl
  have henergy : physicalScheduledEnergy M θB hB N L₀ u (.node k hk C) Q =
      ∫ z, scheduledShapeEnergy (L₀+1) (d+1) (.node k hk C)
        (rootSchedule (r+1+(d+1)) (fun j v => (Q (some (some ⟨j,v⟩))).val))
        (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
          (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
          (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
        (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
          (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z)
        ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
          (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N) := by
    unfold physicalScheduledEnergy
    rw [hd,hparent]
  have hchild (s : Bool) : physicalChildMass M θB hB N L₀ u k hk C s Q =
      (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1)
        (r+1+(d+1)+(if s then 1 else 0)) (C j)
        (fun v => (Q (some (some ⟨j,v⟩))).val+(if s then 1 else 0))
        (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
          (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
          (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
        (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
          (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z)
        ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
          (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)) := by
    cases s <;> simp only [physicalChildMass,physicalScheduledEnergy,
      DepthAverage.coordinateProjection,childCoordinates,DepthAverage.shiftPerm,
      Bool.false_eq_true,ite_false,ite_true,Equiv.refl_apply,hrot,
      he,Nat.add_zero]
  have hold := hchild false
  have hnew := hchild true
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at hold
  simp only [ite_true,show r+1+(d+1)+1=r+1+1+(d+1) by omega] at hnew
  have hg : m = grid (L₀+1) 0 (L₀+1) := gridExponents_cons L₀
  have hbij : Function.Bijective q := (leafHeightCast_bijective ht RawTarget).comp q₀.bijective
  have hfirst : η≤((d+1+r+2:ℕ):ℝ)/((H+1+1+r+1+(d+1):ℕ):ℝ) := by
    have hx := (hQ.1.1 (some none)).1.le
    dsimp only [DepthAverage.normalized] at hx
    rw [he] at hx
    exact hx.trans (div_le_div_of_nonneg_right (by exact_mod_cast (show r+1+(d+1)≤d+1+r+2 by omega)) (by positivity))
  have hcharge := node_frame_charge_uniform H r (d+1) k hk (some none) C
    (fun j => childBranchCoordinates (hk := hk) j) Q had hη hfirst q hbij none v (by simp [v])
  have hpair : pairHistoryMass S m a ≤ (nodeHistoryBudget k hk C:ℝ) := by
    rw [hg,pairHistoryMass_grid (L := L₀+1) (by omega) S a]
    dsimp only [S]
    rw [leaves_splitFrame,node_old_realize_leaves H (r+1+(d+1)+1) k hk C _ had]
    unfold nodeHistoryBudget
    push_cast
    linarith
  have hc : η≤(((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ) := by
    have hx := (hQ.1.1 none).1.le
    dsimp only [DepthAverage.normalized] at hx
    rw [hd] at hx
    exact hx.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hc1 : (((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ)≤1 := by
    apply (div_le_one (by positivity)).mpr
    dsimp only [L₀]
    push_cast
    linarith
  change _ ≤ 2*(2*((L₀+1:ℕ):ℝ)⁻¹+
      |physicalTreeMatrixCovariance (gridExponents L₀) S a M θB hB N u T q|/|J|+
      (2*Real.sqrt _ + physicalNodeShift M θB hB N L₀ u k hk C Q)*
        shiftedCharge (shiftedPrefixDepths (stem BaseNode r) (d+1)) T S
          (v::canonicalMatrixTail t).length/|J|+
      pairHistoryMass S m a*(2*Real.sqrt _)) + _ at hstep
  dsimp only [childBranchCoordinates] at hstep
  rw [← henergy,← hold,← hnew] at hstep
  rw [List.length_cons,canonicalMatrixTail_length] at hstep
  have hcharge' : shiftedCharge (shiftedPrefixDepths (stem BaseNode r) (d+1)) T S (t+1)/|J| ≤
      nodeChargeConstant k hk C η := by
    simp only [J,hg]
    convert hcharge using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [childBranchCoordinates,BaseNode,T,S,t,RawTarget,NewNode,OldNode,L₀]
    congr 4
  have hs := multileaf_scalar_bound
    (δ := ((L₀+1:ℕ):ℝ)⁻¹)
    (err := |physicalTreeMatrixCovariance (gridExponents L₀) S a M θB hB N u T q|/|J|)
    (w' := physicalChildMass M θB hB N L₀ u k hk C true Q) hc hc1
    (physicalScheduledEnergy_nonneg M θB hB N L₀ u _ Q)
    (physicalChildMass_nonneg M θB hB N L₀ u k hk C false Q)
    (physicalNodeShift_nonneg M θB hB N L₀ u k hk C Q) hcharge' hpair
    (physicalChildMass_le_sqrt M θB hB N L₀ u k hk C false Q) (by
      convert hstep using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  exact hs

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
variable {p : ℕ}

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.regularNodeAverageDecidableEq
lemma physicalShapeAverage_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalShapeAverage M θB hB N L u S η :=
  DepthAverage.average_nonneg _ _ (physicalScheduledEnergy_nonneg M θB hB N L u S)

lemma physicalShapeAverage_le_one (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    physicalShapeAverage M θB hB N L u S η≤1 :=
  DepthAverage.average_le_const _ _ zero_le_one
    (fun Q _ => physicalScheduledEnergy_le_one M θB hB N L u S Q)

lemma averaged_multileaf_scalar_bound {α : Type} [Fintype α] [DecidableEq α]
    {L : ℕ} [NeZero L] (D : (α → Fin L) → Prop)
    (F E W W' H : (α → Fin L) → ℝ) {η δ K P k B B' : ℝ}
    (hδ : 0≤δ) (hK : 0≤K) (hP : 0≤P) (hk : 0≤k)
    (hpoint : ∀ Q, D Q → η*F Q≤4*δ+2*E Q+4*K*W' Q+2*K*H Q+(4*P+16*k)*W Q)
    (hW : DepthAverage.average D W≤B) (hW' : DepthAverage.average D W'≤B)
    (hH : DepthAverage.average D H≤B') :
    η*DepthAverage.average D F≤4*δ+2*DepthAverage.average D E+(4*K+4*P+16*k)*B+2*K*B' := by
  have hav := DepthAverage.average_mono D _ _ hpoint
  simp only [DepthAverage.average_add_eq,DepthAverage.average_const_mul] at hav
  have hd : DepthAverage.average D (fun _ => δ)≤δ :=
    DepthAverage.average_le_const _ _ hδ (fun _ _ => le_rfl)
  have hc₀ := mul_le_mul_of_nonneg_left hW (by positivity : 0≤4*P+16*k)
  have hc₁ := mul_le_mul_of_nonneg_left hW' (by positivity : 0≤4*K)
  have hs := mul_le_mul_of_nonneg_left hH (by positivity : 0≤2*K)
  linarith only [hav,hd,hc₀,hc₁,hs]

lemma physicalChildMass_average (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ)) (s : Bool) :
    DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η)
      (fun Q => Real.sqrt (physicalChildMass M θB hB N L u k hk C s Q))≤
      physicalChildrenAverage M θB hB N L u k C η :=
  physical_scheduled_child_moment M θB hB N L u hη hlarge k hk C s

lemma regular_node_average_inequality (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ))
    (S T : (Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) → PrescribedTree (L+1))
    (a : (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) → (S Q).Leaf)
    (q : (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) →
      Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → (T Q).Leaf)
    (J : (Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) → ℝ)
    (hpoint : ∀ Q, regularShapeDomain (.node k hk C) (L+1) η Q →
      η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
        4*((L+1:ℕ):ℝ)⁻¹ +
        2*(|physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB N u (T Q) (q Q)|/|J Q|) +
        4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
        2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
        (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
          Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q)) :
    η*physicalShapeAverage M θB hB N L u (.node k hk C) η ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η) (fun Q =>
        |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB N u (T Q) (q Q)|/|J Q|) +
      (4*nodeChargeConstant k hk C η+4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        physicalChildrenAverage M θB hB N L u k C η +
      2*nodeChargeConstant k hk C η*Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)) := by
  have hc (s : Bool) := physicalChildMass_average M θB hB N L u k hk C hη hlarge s
  have hs := physicalNodeShift_average M θB hB N L u k hk C η (by linarith)
  have hb := averaged_multileaf_scalar_bound
    (regularShapeDomain (.node k hk C) (L+1) η)
    (physicalScheduledEnergy M θB hB N L u (.node k hk C))
    (fun Q => |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB N u (T Q) (q Q)|/|J Q|)
    (fun Q => Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q))
    (fun Q => Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q))
    (physicalNodeShift M θB hB N L u k hk C)
    (η := η) (δ := ((L+1:ℕ):ℝ)⁻¹) (K := nodeChargeConstant k hk C η)
    (P := (nodeHistoryBudget k hk C:ℝ)) (k := (k:ℝ))
    (B := physicalChildrenAverage M θB hB N L u k C η)
    (B' := Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)))
    (by positivity) (nodeChargeConstant_nonneg k hk C hη) (by positivity) (by positivity)
    hpoint (hc false) (hc true) hs
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [physicalShapeAverage]
  congr 3


/-- Uniform averaged producer. All old/target experiments are chosen before N
and u. The two old/delayed child contributions are controlled using full-cube
fibers, never by restricting independently averaged copies to a diagonal. -/
theorem regular_node_average (M : Model p) (θB hB : ℝ) (L : ℕ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ)) :
    let α := Option (ReducedTopology.node k hk C).Vertex
    let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1
    ∃ (S T : (α → Fin (L+1)) → PrescribedTree (L+1))
      (a : (Q : α → Fin (L+1)) → (S Q).Leaf)
      (q : (Q : α → Fin (L+1)) → Option (Fin t) → (T Q).Leaf)
      (J : (α → Fin (L+1)) → ℝ), ∀ (N : ℕ) (u : Spec L × ℕ → ℝ),
    η*physicalShapeAverage M θB hB N L u (.node k hk C) η ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η) (fun Q =>
        |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB N u (T Q) (q Q)|/|J Q|) +
      (4*nodeChargeConstant k hk C η+4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        physicalChildrenAverage M θB hB N L u k C η +
      2*nodeChargeConstant k hk C η*Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)) := by
  classical
  dsimp only
  let D := regularShapeDomain (.node k hk C) (L+1) η
  have hpoint (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
      ∃ (S T : PrescribedTree (L+1)) (a : S.Leaf)
        (q : Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → T.Leaf)
        (J : ℝ), ∀ N u, D Q →
      η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
        4*((L+1:ℕ):ℝ)⁻¹ +
        2*(|physicalTreeMatrixCovariance (gridExponents L) S a M θB hB N u T q|/|J|) +
        4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
        2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
        (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
          Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q) := by
    by_cases hQ : D Q
    · obtain ⟨S,T,a,q,J,h⟩ := regular_node_pointwise M θB hB L k hk C hη (by linarith) Q hQ
      exact ⟨S,T,a,q,J,fun N u _ => h N u⟩
    · exact ⟨single (L+1),single (L+1),singleLeaf (L+1),fun _ => singleLeaf (L+1),1,
        fun _ _ h => (hQ h).elim⟩
  choose S T a q J hpoint using hpoint
  refine ⟨S,T,a,q,J,?_⟩
  intro N u
  exact regular_node_average_inequality M θB hB N L u k hk C hη hlarge S T a q J
    (hpoint · N u)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularCovarianceLimit
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.regularCovarianceLimitDecidableEq
lemma physicalShapeLimsup_nonneg (M : Model p) (θB hB : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalShapeLimsup M θB hB L Ns us S η :=
  unit_limsup_nonneg (fun n => physicalShapeAverage_nonneg M θB hB (Ns n+1) L (us n) S η)
    (fun n => physicalShapeAverage_le_one M θB hB (Ns n+1) L (us n) S η)

lemma physicalShapeLimsup_leaf {M : Model p} {θB hB : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : ScheduledControl M θB hB L Ns us)
    {η : ℝ} (hη : 0<η) :
    physicalShapeLimsup M θB hB L Ns us .leaf η≤((L+1:ℕ):ℝ)⁻¹/η := by
  apply le_of_forall_pos_le_add
  intro t ht
  exact limsup_le_of_le (IsCoboundedUnder.of_frequently_ge
    ((Eventually.of_forall (fun n => physicalShapeAverage_nonneg M θB hB (Ns n+1) L (us n) .leaf η)).frequently))
    (h.singleton η hη t ht)

/-- The full node recursion after the N-limit; the charge is uniform in L,
and the only signed-covariance errors have disappeared at fixed grid. -/
theorem physicalShapeLimsup_node {M : Model p} {θB hB : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : ScheduledControl M θB hB L Ns us)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ)) :
    η*physicalShapeLimsup M θB hB L Ns us (.node k hk C) η ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*nodeChargeConstant k hk C η*Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)) +
      (4*nodeChargeConstant k hk C η+4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (physicalShapeLimsup M θB hB L Ns us (C j) (η/2))) := by
  obtain ⟨S,T,a,q,J,hav⟩ := regular_node_average M θB hB L k hk C hη hlarge
  have he := h.matrix (Option (ReducedTopology.node k hk C).Vertex)
    (regularShapeDomain (.node k hk C) (L+1) η) S T a
    (fun _ => 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1) (fun _ => by omega) q J
  have hK := nodeChargeConstant_nonneg k hk C hη
  apply limsup_finite_sqrt_bound
    (fun n => physicalShapeAverage M θB hB (Ns n+1) L (us n) (.node k hk C) η)
    _ (fun j n => physicalShapeAverage M θB hB (Ns n+1) L (us n) (C j) (η/2))
    hη (by positivity) (by positivity)
    (fun n => physicalShapeAverage_nonneg M θB hB (Ns n+1) L (us n) _ η)
    (fun n => physicalShapeAverage_le_one M θB hB (Ns n+1) L (us n) _ η)
    (fun j n => physicalShapeAverage_le_one M θB hB (Ns n+1) L (us n) (C j) (η/2)) he
  intro n
  have hh := hav (Ns n+1) (us n)
  dsimp only [physicalChildrenAverage] at hh
  linarith only [hh]

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularCovarianceConvergence
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
variable {p : ℕ}

noncomputable local instance regularCovarianceConvergenceDecidableEq_r33125b_1 (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
lemma grid_inverse_tendsto : Tendsto (fun L : ℕ => ((L+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)

lemma eventually_large_grid {η : ℝ} (hη : 0<η) :
    ∀ᶠ L : ℕ in atTop, 4<η*((L+1:ℕ):ℝ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (4/η)
  filter_upwards [eventually_ge_atTop n] with L hL
  have hc : (n:ℝ)≤((L+1:ℕ):ℝ) := by exact_mod_cast (show n≤L+1 by omega)
  have hd := (div_lt_iff₀ hη).mp (hn.trans_le hc)
  simpa only [mul_comm] using hd

/-- Structural, finite-topology closure of the covariance recursion. The
same physical selection is used for every child, with N taken to infinity
before the mesh is refined. -/
theorem physicalShapeLimsup_tendsto_oai (M : Model p) (θB hB : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, ScheduledControl M θB hB L (Ns L) (us L))
    (S : ReducedTopology) {η : ℝ} (hη : 0<η) :
    Tendsto (fun L => physicalShapeLimsup M θB hB L (Ns L) (us L) S η) atTop (𝓝 0) := by
  induction S generalizing η with
  | leaf =>
    apply squeeze_zero (fun L => physicalShapeLimsup_nonneg M θB hB L (Ns L) (us L) .leaf η)
      (fun L => physicalShapeLimsup_leaf (hcontrol L) hη)
    simpa using grid_inverse_tendsto.div_const η
  | node k hk C ih =>
    let B := 4*nodeChargeConstant k hk C η+4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ)
    let RHS (L : ℕ) := (4*((L+1:ℕ):ℝ)⁻¹+
      2*nodeChargeConstant k hk C η*Real.sqrt (nodeShiftBudget k C/(L+1:ℕ))+
      B*Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (physicalShapeLimsup M θB hB L (Ns L) (us L) (C j) (η/2))))/η
    have hsum : Tendsto (fun L => ∑ j, Real.sqrt
        (physicalShapeLimsup M θB hB L (Ns L) (us L) (C j) (η/2))) atTop (𝓝 0) := by
      have hh := tendsto_finsetSum (Finset.univ : Finset (Fin k)) (fun j _ =>
        (ih j (half_pos hη)).sqrt)
      simpa using hh
    have hshift : Tendsto (fun L : ℕ => Real.sqrt (nodeShiftBudget k C/(L+1:ℕ))) atTop (𝓝 0) := by
      have hh := (grid_inverse_tendsto.const_mul (nodeShiftBudget k C)).sqrt
      simpa [div_eq_mul_inv] using hh
    have hR : Tendsto RHS atTop (𝓝 0) := by
      have hh := (((grid_inverse_tendsto.const_mul 4).add
        (hshift.const_mul (2*nodeChargeConstant k hk C η))).add
        (((hsum.const_mul (k:ℝ)).sqrt).const_mul B)).div_const η
      simpa [RHS] using hh
    apply squeeze_zero' (Eventually.of_forall (fun L =>
      physicalShapeLimsup_nonneg M θB hB L (Ns L) (us L) (.node k hk C) η)) _ hR
    filter_upwards [eventually_large_grid hη] with L hL
    apply (le_div_iff₀ hη).mpr
    rw [mul_comm]
    exact physicalShapeLimsup_node (hcontrol L) k hk C hη hL

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.physicalShapeLimsup_tendsto_oai := @OAI.DilutedSpinGlass.UniversalDictionary.physicalShapeLimsup_tendsto_oai
