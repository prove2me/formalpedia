-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:04:34.538758+00:00
-- url     : https://prove2.me/submissions/74a544e2-a836-4bd0-a5ac-b247788c7f51

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

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

/-- Matrix Cauchy-Schwarz with exactly the manuscript's normalization. -/
theorem normalized_abs_sum_le (C : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, |C i j|) / (n : ℝ)^2 ≤
      Real.sqrt ((∑ i, ∑ j, C i j ^ 2) / (n : ℝ)^2) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsq : (∑ i, ∑ j, |C i j|)^2 ≤ (n : ℝ)^2 * (∑ i, ∑ j, C i j ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun ij : Fin n × Fin n => |C ij.1 ij.2|)
    simpa [Fintype.sum_prod_type, sq_abs, pow_two] using h
  apply Real.le_sqrt_of_sq_le
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos (sq_pos_of_pos hn') 2) (sq_pos_of_pos hn')).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (n : ℝ))]

/-- The exact second moment if the other vector is held fixed. -/
theorem centered_contraction_identity (X : Ω → Fin n → ℝ) (b : Fin n → ℝ) :
    P.expect (fun x => (dot (fun i => X x i - P.expect (fun y => X y i)) b)^2) =
      (∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j) * (b i * b j)) /
        (n : ℝ)^2 := by
  simp_rw [dot_sq, expect_div, expect_fintype_sum, expect_mul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_centered]

/-- decor:contraction-bound, before the last square root, for a fixed multiplier. -/
theorem centered_contraction_bound (X : Ω → Fin n → ℝ) (b : Fin n → ℝ)
    (hb : ∀ i, |b i| ≤ 1) :
    P.expect (fun x => (dot (fun i => X x i - P.expect (fun y => X y i)) b)^2) ≤
      Real.sqrt (P.covarianceEnergy X) := by
  rw [centered_contraction_identity]
  apply le_trans _ (normalized_abs_sum_le (fun i j =>
    P.covariance (fun x => X x i) (fun x => X x j)))
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ |P.covariance (fun x => X x i) (fun x => X x j) * (b i * b j)| := le_abs_self _
    _ = |P.covariance (fun x => X x i) (fun x => X x j)| * (|b i| * |b j|) := by
      simp only [abs_mul]
    _ ≤ |P.covariance (fun x => X x i) (fun x => X x j)| * (1 * 1) := by
      gcongr <;> exact hb _
    _ = _ := by ring

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

/-- Differentiation commutes with a finite path kernel. -/
theorem hasDerivAt_expect {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {u : ℝ}
    (h : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => P.expect (f t)) (P.expect f') u := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun x _ => (h x).const_mul (P.weight x))
  have heq : (∑ x, fun t => P.weight x * f t x) = (fun t => P.expect (f t)) := by
    funext t
    simp only [Finset.sum_apply, expect]
  rw [heq] at hd
  exact hd

/-- First variation of a power-mean step: the derivative is the tilted score. -/
theorem hasDerivAt_logMean {m : ℝ} (hm : m ≠ 0)
    {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {u : ℝ}
    (h : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => P.logMean m (f t)) ((P.tilt m (f u)).expect f') u := by
  have he := P.hasDerivAt_expect (fun x => ((h x).const_mul m).exp)
  have hl := (he.log (ne_of_gt (P.expMoment_pos m (f u)))).div_const m
  change HasDerivAt (fun t => P.logMean m (f t)) _ u at hl
  suffices heqv : (P.tilt m (f u)).expect f' =
      (P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) / P.expMoment m (f u)) / m by
    rw [heqv]
    exact hl
  rw [tilt_expect]
  have heq : P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) =
      m * P.expect (fun x => Real.exp (m * f u x) * f' x) := by
    rw [← expect_mul_left]
    exact P.expect_congr (fun x => by ring)
  rw [heq]
  field_simp


/-- The edge-density form of the normalized tilted finite kernel. -/
theorem tilt_weight {m : ℝ} (hm : m ≠ 0) (f : Ω → ℝ) (x : Ω) :
    (P.tilt m f).weight x = P.weight x * Real.exp (m * (f x - P.logMean m f)) := by
  have hlog : m * P.logMean m f = Real.log (P.expMoment m f) := by
    unfold logMean
    field_simp
  rw [mul_sub, hlog, Real.exp_sub, Real.exp_log (P.expMoment_pos m f)]
  simp only [tilt, mul_div_assoc]

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
-- module Solutions.OAIQ041_DS.DilutedSpin_KernelTower
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

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

/-- First variation through the entire finite hierarchy, with all exponents
and all original path-dependent priors retained. -/
theorem hasDerivAt_backwardLog (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (hm : ∀ i, m i ≠ 0)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => backwardLog n T m (f t))
      ((law n (tilt n T m (f u))).expect f') u := by
  induction n with
  | zero =>
    rw [law_zero_expect (Ω := Ω)]
    exact hf ()
  | succ n ih =>
    have hs := fun x => ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
      (fun y => hf (x,y))
    rw [law_succ_expect (Ω := Ω) n]
    simpa only [backwardLog, tilt] using
      T.1.hasDerivAt_logMean (hm 0) hs


theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeSampling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

/-- Exact joint law after insertion, expressed without division by the old
weight. This handles zero-probability paths and every prescribed tree. -/
theorem sampleLaw_tilt_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (f : FinitePath Ω n → ℝ)
    (x : Sample Ω S) :
    (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) f)).weight x =
      (sampleLaw S T).weight x * Real.exp
        (vertexPotential S T m f x - m 0 * KernelTower.backwardLog n T (fun j => m j.succ) f) := by
  induction S with
  | leaf => simp [sampleLaw, vertexPotential, KernelTower.unitLaw, KernelTower.backwardLog]
  | @node n k C ih =>
    let F := fun z => KernelTower.backwardLog n (T.2 z)
      (fun j => m j.succ.succ) (fun y => f (z,y))
    let B := KernelTower.backwardLog (n+1) T (fun j => m j.succ) f
    let V := fun i => vertexPotential (C i) (T.2 (x i).1) (fun j => m j.succ)
      (fun y => f ((x i).1,y)) (x i).2
    have hedge : ∀ i, ((T.1.tilt (m 1) F).bind (fun z => sampleLaw (C i)
        (KernelTower.tilt n (T.2 z) (fun j => m j.succ.succ) (fun y => f (z,y))))).weight (x i) =
        (T.1.bind (fun z => sampleLaw (C i) (T.2 z))).weight (x i) *
          Real.exp (V i - m 1 * B) := by
      intro i
      simp only [FiniteLaw.bind]
      rw [FiniteLaw.tilt_weight _ (show m 1 ≠ 0 by simpa using hm 0), ih i (T.2 (x i).1) (fun j => m j.succ)
        (fun j => hm j.succ) (fun y => f ((x i).1,y)) (x i).2]
      change (_ * Real.exp (m 1 * (F (x i).1 - B))) *
        (_ * Real.exp (V i - m 1 * F (x i).1)) = _
      rw [mul_mul_mul_comm, ← Real.exp_add]
      congr 2
      ring
    change (∏ i, ((T.1.tilt (m 1) F).bind (fun z => sampleLaw (C i)
        (KernelTower.tilt n (T.2 z) (fun j => m j.succ.succ) (fun y => f (z,y))))).weight (x i)) = _
    simp_rw [hedge]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    change (_ * Real.exp (∑ i, (V i - m 1 * B))) =
      _ * Real.exp (((m 0 - (k : ℝ) * m 1) * B + ∑ i, V i) - m 0 * B)
    congr 2
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring

/-- At the tree root there is no incoming edge. This is the self-contained,
finite-kernel version of tree:density, with exactly its vertex exponents. -/
theorem sampleLaw_tilt_density {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω S) :
    (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) f)).weight x =
      (sampleLaw S T).weight x * Real.exp (vertexPotential S T m f x) := by
  rw [sampleLaw_tilt_weight S T m hm f x, hroot, zero_mul, sub_zero]

/-- Differentiate the entire prescribed tree density, without assuming all
sampled prefixes are distinct or all original kernel weights positive. -/
theorem hasDerivAt_vertexPotential {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u) (x : Sample Ω S) :
    HasDerivAt (fun t => vertexPotential S T m (f t) x)
      (vertexScore S T m (f u) f' x) u := by
  induction S with
  | leaf => exact (hf ()).const_mul (m 0)
  | @node n k C ih =>
    have ha := (KernelTower.hasDerivAt_backwardLog (n+1) T (fun j => m j.succ) hm hf).const_mul
      (m 0 - (k : ℝ) * m 1)
    have hb := HasDerivAt.sum (u := Finset.univ) (fun i _ => ih i (T.2 (x i).1)
      (fun j => m j.succ) (fun j => hm j.succ) (fun y => hf ((x i).1,y)) (x i).2)
    have heq : (∑ i, (fun t => vertexPotential (C i) (T.2 (x i).1) (fun j => m j.succ)
        (fun y => f t ((x i).1,y)) (x i).2)) =
        (fun t => ∑ i, vertexPotential (C i) (T.2 (x i).1) (fun j => m j.succ)
          (fun y => f t ((x i).1,y)) (x i).2) := by
      funext t
      simp only [Finset.sum_apply]
    rw [heq] at hb
    exact ha.add hb

/-- Joint-law density in expectation form; physical root remains fixed. -/
theorem sampleLaw_tilt_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (f : FinitePath Ω n → ℝ) (G : Sample Ω S → ℝ) :
    (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) f)).expect G =
      (sampleLaw S T).expect (fun x => G x * Real.exp (vertexPotential S T m f x)) := by
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro x _
  rw [sampleLaw_tilt_density S T m hm hroot]
  ring

/-- Tree differentiation rule, including a parameter-dependent test. Choosing
G as a product of canceled replica factors yields the protected-leaf rule. -/
theorem hasDerivAt_sampleLaw_tilt_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ}
    {G : ℝ → Sample Ω S → ℝ} {G' : Sample Ω S → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u)
    (hG : ∀ x, HasDerivAt (fun t => G t x) (G' x) u) :
    HasDerivAt (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect (G t))
      ((sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => G' x + G u x * vertexScore S T m (f u) f' x)) u := by
  simp_rw [sampleLaw_tilt_expect S T m hm hroot]
  have hd := (sampleLaw S T).hasDerivAt_expect (fun x =>
    (hG x).mul (hasDerivAt_vertexPotential S T m hm hf x).exp)
  apply hd.congr_deriv
  apply (sampleLaw S T).expect_congr
  intro x
  ring

omit [Fintype Ω] in
theorem hasDerivAt_protectedLog {n : ℕ} (S : PrescribedTree n) (C : Finset (Leaf S))
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u) (x : Sample Ω S) :
    HasDerivAt (fun t => protectedLog S C (f t) x) (protectedLog S C f' x) u := by
  have hd := HasDerivAt.sum (u := C) (fun a _ => hf (pathAt S a x))
  have heq : (∑ a ∈ C, (fun t => f t (pathAt S a x))) =
      (fun t => protectedLog S C (f t) x) := by
    funext t
    simp only [Finset.sum_apply, protectedLog]
  rw [heq] at hd
  exact hd

 
theorem hasDerivAt_protected_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (C : Finset (Leaf S)) (G : Sample Ω S → ℝ)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u) :
    HasDerivAt (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G x * Real.exp (-protectedLog S C (f t) x)))
      ((sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => (G x * Real.exp (-protectedLog S C (f u) x)) *
          (vertexScore S T m (f u) f' x - protectedLog S C f' x))) u := by
  have hg := fun x => ((hasDerivAt_protectedLog S C hf x).neg.exp).const_mul (G x)
  have hd := hasDerivAt_sampleLaw_tilt_expect S T m hm hroot hf hg
  apply hd.congr_deriv
  apply FiniteLaw.expect_congr
  intro x
  change G x * (Real.exp (-protectedLog S C (f u) x) * -protectedLog S C f' x) +
    G x * Real.exp (-protectedLog S C (f u) x) * vertexScore S T m (f u) f' x = _
  ring

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

variable {Ω : Type} [Fintype Ω]

/-- Resolves the differentiated density into terminal contributions and actual
fresh conditional path expectations. No diagonal identification is made. -/
theorem vertexScore_decomposition {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (f D : FinitePath Ω n → ℝ) (x : Sample Ω S) :
    vertexScore S T m f D x =
      m (Fin.last n) * (∑ a : Leaf S, D (pathAt S a x)) +
      ∑ v : Internal S, gamma S m v *
        freshEval S (KernelTower.tilt n T (fun j => m j.succ) f) v D x := by
  induction S with
  | leaf =>
    change m 0 * D () = m 0 * (∑ a : Unit, D ()) + ∑ v : Empty, _
    simp
  | @node n k C ih =>
    let T' := KernelTower.tilt (n+1) T (fun j => m j.succ) f
    have hL : (∑ a : Leaf (.node k C), D (pathAt (.node k C) a x)) =
        ∑ i, ∑ a : Leaf (C i), D ((x i).1, pathAt (C i) a (x i).2) :=
      Fintype.sum_sigma _
    have hI : (∑ v : Internal (.node k C), gamma (.node k C) m v *
        freshEval (.node k C) T' v D x) =
        (m 0 - (k : ℝ) * m 1) * (KernelTower.law (n+1) T').expect D +
        ∑ i, ∑ v : Internal (C i), gamma (C i) (fun j => m j.succ) v *
          freshEval (C i) (KernelTower.tilt n (T.2 (x i).1)
            (fun j => m j.succ.succ) (fun y => f ((x i).1,y))) v
              (fun y => D ((x i).1,y)) (x i).2 := by
      change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
      rw [Fintype.sum_option, Fintype.sum_sigma]
      rfl
    change (m 0 - (k : ℝ) * m 1) * (KernelTower.law (n+1) T').expect D +
      (∑ i, vertexScore (C i) (T.2 (x i).1) (fun j => m j.succ)
        (fun y => f ((x i).1,y)) (fun y => D ((x i).1,y)) (x i).2) = _
    rw [hL, hI]
    simp_rw [ih]
    simp only [Finset.sum_add_distrib, Fin.succ_last, Finset.mul_sum]
    ring

/-- Exact finite-kernel form of the protected-leaf differentiation rule.
The second line is the expectation on a fresh extended path, conditional on
its shared prefix. The canceled leaves are removed, not merely bounded. -/
theorem protected_leaf_extension_rule {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    [DecidableEq (Leaf S)] (C : Finset (Leaf S)) (G : Sample Ω S → ℝ)
    {f : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (D y) u) :
    HasDerivAt (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G x * Real.exp (-protectedLog S C (f t) x)))
      ((sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => (G x * Real.exp (-protectedLog S C (f u) x)) *
          ((∑ a ∈ Finset.univ \ C, D (pathAt S a x)) +
            ∑ v : Internal S, gamma S m v *
              freshEval S (KernelTower.tilt n T (fun j => m j.succ) (f u)) v D x))) u := by
  classical
  apply (hasDerivAt_protected_expect S T m hm hroot C G hf).congr_deriv
  apply FiniteLaw.expect_congr
  intro x
  rw [vertexScore_decomposition, hend, one_mul]
  simp only [protectedLog]
  have hh : (∑ a ∈ Finset.univ \ C, D (pathAt S a x)) +
      (∑ a ∈ C, D (pathAt S a x)) = ∑ a, D (pathAt S a x) :=
    Finset.sum_sdiff (Finset.subset_univ C)
  rw [← hh]
  ring

end DilutedSpinGlass.PrescribedTree

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

/-- Split off the new first child at a root attachment. -/
theorem expect_pi_cons {n : ℕ} {α : Fin (n+1) → Type*} [∀ i, Fintype (α i)]
    (Q : (i : Fin (n+1)) → FiniteLaw (α i)) (H : ((i : Fin (n+1)) → α i) → ℝ) :
    (pi Q).expect H = (Q 0).expect (fun a =>
      (pi (fun j : Fin n => Q j.succ)).expect (fun rest => H (Fin.cons a rest))) := by
  classical
  simp only [expect, pi]
  rw [← (Fin.consEquiv α).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [Fin.prod_univ_succ]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  ring_nf
  rfl

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
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeDerivatives
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

theorem leafSum_eq_sum {n : ℕ} (S : PrescribedTree n)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω S) :
    leafSum S f x = ∑ a : Leaf S, f (pathAt S a x) := by
  induction S with
  | leaf =>
    change f () = ∑ _ : Unit, f ()
    simp
  | @node n k C ih =>
    change (∑ i, leafSum (C i) (fun y => f ((x i).1,y)) (x i).2) = _
    have hL : (∑ a : Leaf (.node k C), f (pathAt (.node k C) a x)) =
        ∑ i, ∑ a : Leaf (C i), f ((x i).1,pathAt (C i) a (x i).2) := Fintype.sum_sigma _
    rw [hL]
    exact Finset.sum_congr rfl (fun i _ => ih i _ _)

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
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductTowers
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
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- A mark block not present in a log weight integrates out, before or after
any one power-mean tilt. -/
theorem logMean_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1) = P.logMean m f := by
  simp [logMean, expMoment]

theorem tilt_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).tilt m (fun z => f z.1) =
      (P.tilt m f).bind (fun _ => Q) := by
  ext z
  change P.weight z.1 * Q.weight z.2 * Real.exp (m*f z.1) /
      (P.bind (fun _ => Q)).expMoment m (fun z => f z.1) =
      (P.weight z.1 * Real.exp (m*f z.1) / P.expMoment m f) * Q.weight z.2
  have hh : (P.bind (fun _ => Q)).expMoment m (fun z => f z.1) = P.expMoment m f := by
    simp [expMoment]
  rw [hh]
  ring
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)) = backwardLog n T m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, prod, pathFst]
    have hh : (fun z : Ω × Λ => backwardLog n
        (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
        (fun y => f (z.1, pathFst n y))) =
        (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
          (fun y => f (z.1,y))) := by
      funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
    rw [hh]
    exact FiniteLaw.logMean_bind_fst T.1 U.1 (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

theorem tilt_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    tilt n (prod n T U) m (fun y => f (pathFst n y)) = prod n (tilt n T m f) U := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change (T.1.bind (fun _ => U.1)).tilt (m 0)
        (fun z => backwardLog n (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
          (fun y => f (z.1,pathFst n y))) =
        (T.1.tilt (m 0) (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
          (fun y => f (x,y)))).bind (fun _ => U.1)
      have hh : (fun z : Ω × Λ => backwardLog n
          (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
          (fun y => f (z.1, pathFst n y))) =
          (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
            (fun y => f (z.1,y))) := by
        funext z
        exact backwardLog_prod_fst n (T.2 z.1) (U.2 z.2) (fun j => m j.succ)
          (fun y => f (z.1,y))
      rw [hh]
      exact FiniteLaw.tilt_bind_fst T.1 U.1 (m 0)
        (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
    · funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
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

noncomputable local instance instDecidable_4_r802ef5_1 (p : Prop) : Decidable p := Classical.propDecidable p
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

noncomputable local instance instDecidable_6_r802ef5_1 (p : Prop) : Decidable p := Classical.propDecidable p
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
namespace DilutedSpinGlass.MarkSelector
open scoped BigOperators

/-- Independent vertex marks select sharing of the vertex, not equality of spins. -/
theorem pair_selector {V : Type*} [Fintype V] [DecidableEq V] (a b : V) :
    (FiniteLaw.pi (fun _ : V => rademacher)).expect
      (fun x => sign (x a) * sign (x b)) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    simp only [sign_sq,FiniteLaw.expect_const,ite_true]
  · rw [ite_eq_right hab]
    let f (v : V) (x : Bool) : ℝ :=
      (if v = a then sign x else 1) * (if v = b then sign x else 1)
    have he (x : V → Bool) : (∏ v, f v (x v)) = sign (x a) * sign (x b) := by
      simp only [f,Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,ite_true]
    simp_rw [← he]
    rw [FiniteLaw.expect_pi_product]
    apply Finset.prod_eq_zero (i := a) (Finset.mem_univ _)
    simp only [f,ite_true,ite_eq_right hab,mul_one,mean_sign]

/-- Different requested color pairs use separate independent coordinates. -/
theorem requirements_selector {R V : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (a b : R → V) :
    (FiniteLaw.pi (fun _ : R => FiniteLaw.pi (fun _ : V => rademacher))).expect
      (fun x => ∏ r, sign (x r (a r)) * sign (x r (b r))) =
      ∏ r, if a r = b r then (1 : ℝ) else 0 := by
  calc
    _ = ∏ r, (FiniteLaw.pi (fun _ : V => rademacher)).expect
        (fun y => sign (y (a r)) * sign (y (b r))) :=
      FiniteLaw.expect_pi_product (α := fun _ : R => V → Bool)
        (fun _ : R => FiniteLaw.pi (fun _ : V => rademacher))
        (fun (r : R) (y : V → Bool) => sign (y (a r)) * sign (y (b r)))
    _ = _ := Finset.prod_congr rfl (fun r _ => pair_selector (a r) (b r))

end DilutedSpinGlass.MarkSelector

end

end

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
noncomputable local instance (priority := 2000) instDecidableEqSigma_r802ef5_1 {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _
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

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree

variable {Ω : Type} [Fintype Ω]

/-- A parameter-dependent old test can be differentiated without changing
any of the actual tree sampling kernels. -/
theorem hasDerivAt_protected_expect_varying {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (C : Finset (Leaf S)) {G : ℝ → Sample Ω S → ℝ} {G' : Sample Ω S → ℝ}
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u)
    (hG : ∀ x, HasDerivAt (fun t => G t x) (G' x) u) :
    HasDerivAt (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G t x * Real.exp (-protectedLog S C (f t) x)))
      ((sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => G' x * Real.exp (-protectedLog S C (f u) x)) +
       (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => (G u x * Real.exp (-protectedLog S C (f u) x)) *
          (vertexScore S T m (f u) f' x - protectedLog S C f' x))) u := by
  have hg := fun x => (hG x).mul ((hasDerivAt_protectedLog S C hf x).neg.exp)
  have hd := hasDerivAt_sampleLaw_tilt_expect S T m hm hroot hf hg
  apply hd.congr_deriv
  rw [← FiniteLaw.expect_add]
  apply FiniteLaw.expect_congr
  intro x
  change G' x * Real.exp (-protectedLog S C (f u) x) +
    G u x * (Real.exp (-protectedLog S C (f u) x) * -protectedLog S C f' x) +
    G u x * Real.exp (-protectedLog S C (f u) x) * vertexScore S T m (f u) f' x = _
  ring

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem leafSum_mono {n : ℕ} (S : PrescribedTree n) {f g : FinitePath Ω n → ℝ}
    (h : ∀ y, f y ≤ g y) (x : Sample Ω S) : leafSum S f x ≤ leafSum S g x := by
  simp only [leafSum_eq_sum]
  exact Finset.sum_le_sum (fun a _ => h _)

theorem fullyProtected_zero {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : FinitePath Ω n → ℝ) (G : Sample Ω S → ℝ) :
    fullyProtected S T m D G 0 = (sampleLaw S T).expect G := by
  simp [fullyProtected, KernelTower.tilt_const n T _ hm, leafSum_const]

theorem anchorEval_zero {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : FinitePath Ω n → ℝ) {ι : Type} (A : Finset ι)
    (U : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ) :
    anchorEval S T m D A U G 0 = (sampleLaw S T).expect G := by
  simp [anchorEval, fullyProtected_zero S T m hm]

omit [Fintype Ω] in
/-- The denominator in the protected tree rule is uniformly bounded on a
fixed real neighborhood of zero, independently of all kernels and depth. -/
theorem protected_density_bound {n : ℕ} (S : PrescribedTree n)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {t : ℝ} (ht : |t| ≤ 1/2) (x : Sample Ω S) :
    Real.exp (-leafSum S (fun y => Real.log (1+t*D y)) x) ≤ (2:ℝ) ^ leaves S := by
  have hlow (y : FinitePath Ω n) : (1:ℝ)/2 ≤ 1+t*D y := by
    have ha : |t * D y| ≤ 1/2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hD y) (abs_nonneg t)).trans (by simpa using ht)
    have := (abs_le.mp ha).1
    linarith
  have hh := leafSum_mono S (f := fun _ => -Real.log 2)
    (g := fun y => Real.log (1+t*D y)) (fun y => by
      have h := Real.strictMonoOn_log.monotoneOn (show (1:ℝ)/2 ∈ Set.Ioi 0 by norm_num)
        (show 1+t*D y ∈ Set.Ioi 0 by change 0 < 1+t*D y; linarith [hlow y]) (hlow y)
      simpa [Real.log_div] using h) x
  rw [leafSum_const] at hh
  calc
    Real.exp (-leafSum S (fun y => Real.log (1+t*D y)) x) ≤
        Real.exp ((leaves S : ℝ) * Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = (2:ℝ) ^ leaves S := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]

theorem abs_fullyProtected_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    (G : Sample Ω S → ℝ) {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B)
    (ht : |t| ≤ 1/2) : |fullyProtected S T m D G t| ≤ B * (2:ℝ) ^ leaves S := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (hG x) (protected_density_bound S D hD ht x) (Real.exp_pos _).le hB

theorem abs_anchorEval_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {ι : Type} (A : Finset ι) (U : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B)
    (ht : |t| ≤ 1/2) : |anchorEval S T m D A U G t| ≤ B * (2:ℝ) ^ (leaves S + A.card) := by
  have hprod (x : Sample Ω S) : |∏ i ∈ A, (1+t*D (U i x))| ≤ (2:ℝ)^A.card := by
    rw [Finset.abs_prod]
    calc
      (∏ i ∈ A, |1+t*D (U i x)|) ≤ ∏ _i ∈ A, (2:ℝ) := Finset.prod_le_prod
        (fun i _ => abs_nonneg _) (fun i _ => by
          have hterm := abs_add_le (1:ℝ) (t*D (U i x))
          have ha := mul_le_mul_of_nonneg_left (hD (U i x)) (abs_nonneg t)
          rw [← abs_mul, mul_one] at ha
          simp only [abs_one] at hterm
          linarith)
      _ = (2:ℝ)^A.card := by simp
  have hh := abs_fullyProtected_le S T m D hD (fun x => G x * ∏ i ∈ A, (1+t*D (U i x)))
    (B := B * (2:ℝ)^A.card) (by positivity) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hG x) (hprod x) (abs_nonneg _) hB) ht
  simpa only [anchorEval, pow_add, mul_assoc, mul_comm, mul_left_comm] using hh

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem derivativeBound_nonneg (q k : ℕ) : 0 ≤ derivativeBound q k := by
  induction k generalizing q with
  | zero => exact pow_nonneg (by norm_num) _
  | succ k ih => exact mul_nonneg (Nat.cast_nonneg _) (ih _)

theorem derivativeBound_mono (k : ℕ) : Monotone (fun q => derivativeBound q k) := by
  induction k with
  | zero => exact fun a b hab => pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hab
  | succ k ih =>
    intro a b hab
    exact mul_le_mul (by exact_mod_cast hab) (ih (Nat.add_le_add_right hab 1))
      (derivativeBound_nonneg _ _) (Nat.cast_nonneg _)

variable {Ω : Type} [Fintype Ω]

/-- Uniform real control of the full OLD-or-FRESH derivative expansion.
No depth, number of kernel states, or base-disorder law enters the bound. -/
theorem abs_anchorIterate_le {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (hroot : m 0 = 0)
    (hend : m (Fin.last n) = 1) (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {ι : Type} [DecidableEq ι] (k : ℕ) (S : PrescribedTree n) (A : Finset ι)
    (U : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B) (ht : |t| ≤ 1/2) :
    |anchorIterate T m D k S A U G t| ≤ B * derivativeBound (leaves S + A.card) k := by
  induction k generalizing S A with
  | zero => exact abs_anchorEval_le S T m D hD A U G hB hG ht
  | succ k ih =>
    let q := leaves S + A.card
    let C := derivativeBound (q+1) k
    have hold (i : ι) :
        |anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t| ≤ B*C := by
      apply (ih S (A.erase i) U _ (fun x => by
        rw [abs_mul]
        exact (mul_le_mul (hG x) (hD _) (abs_nonneg _) hB).trans (by simp))).trans
      apply mul_le_mul_of_nonneg_left _ hB
      exact derivativeBound_mono k (by
        have hc := Finset.card_le_card (Finset.erase_subset i A)
        dsimp [q]
        omega)
    have hfresh (v : Internal S) :
        |anchorIterate T m D k (grow S v) A (fun i x => U i (oldSample S v x))
          (fun x => G (oldSample S v x) * D (newPath S v x)) t| ≤ B*C := by
      have hh := ih (grow S v) A (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) (fun x => by
        rw [abs_mul]
        exact (mul_le_mul (hG _) (hD _) (abs_nonneg _) hB).trans (by simp))
      simpa only [C, q, leaves_grow, Nat.add_right_comm, Nat.add_assoc] using hh
    have h₁ : |∑ i ∈ A, anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t| ≤
        (A.card:ℝ)*(B*C) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        (∑ i ∈ A, |anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t|)
          ≤ ∑ _i ∈ A, B*C := Finset.sum_le_sum (fun i _ => hold i)
        _ = _ := by simp
    have h₂ : |∑ v : Internal S, gamma S m v * anchorIterate T m D k (grow S v) A
        (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) t| ≤
        (leaves S:ℝ)*(B*C) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        (∑ v : Internal S, |gamma S m v * anchorIterate T m D k (grow S v) A
          (fun i x => U i (oldSample S v x))
          (fun x => G (oldSample S v x) * D (newPath S v x)) t|)
          ≤ ∑ v : Internal S, |gamma S m v| * (B*C) := by
            apply Finset.sum_le_sum
            intro v _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hfresh v) (abs_nonneg _)
        _ = _ := by rw [← Finset.sum_mul, sum_abs_gamma S m hm hpos hroot hend]
    exact ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by
      dsimp [C, q, derivativeBound]
      push_cast
      ring)

end DilutedSpinGlass.PrescribedTree

open Filter Set
open scoped Topology BigOperators

end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω Λ : Type}

variable [Fintype Ω] [Fintype Λ]

lemma sampleLaw_prod_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (U : KernelTower Λ n) (x : Sample (Ω × Λ) S) :
    (S.sampleLaw (KernelTower.prod n T U)).weight x =
      (S.sampleLaw T).weight (sampleFst S x) * (S.sampleLaw U).weight (sampleSnd S x) := by
  induction S with
  | leaf => simp [sampleLaw,KernelTower.unitLaw]
  | @node n k C ih =>
    change (∏ i, (T.1.weight (x i).1.1 * U.1.weight (x i).1.2) *
        ((C i).sampleLaw (KernelTower.prod n (T.2 (x i).1.1) (U.2 (x i).1.2))).weight (x i).2) =
      (∏ i, T.1.weight (x i).1.1 * ((C i).sampleLaw (T.2 (x i).1.1)).weight (sampleFst (C i) (x i).2)) *
      (∏ i, U.1.weight (x i).1.2 * ((C i).sampleLaw (U.2 (x i).1.2)).weight (sampleSnd (C i) (x i).2))
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [ih]
    ring

/-- Fresh mark samples are genuinely independent of every old physical/mark
sample in a prescribed tree, not merely of a single replica. -/
lemma sampleExpect_prod {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (U : KernelTower Λ n) (f : Sample (Ω × Λ) S → ℝ) :
    (S.sampleLaw (KernelTower.prod n T U)).expect f =
      (S.sampleLaw T).expect (fun x => (S.sampleLaw U).expect (fun y => f (samplePair S x y))) := by
  unfold FiniteLaw.expect
  rw [show (∑ x, (S.sampleLaw (KernelTower.prod n T U)).weight x * f x) =
      ∑ z : Sample Ω S × Sample Λ S,
        (S.sampleLaw T).weight z.1 * (S.sampleLaw U).weight z.2 * f (samplePair S z.1 z.2) from
    Fintype.sum_equiv (sampleProdEquiv S) _ _ (fun x => by
      simp only [sampleProdEquiv,Equiv.coe_fn_mk,samplePair_projections,sampleLaw_prod_weight])]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma expect_prod_separated {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (U : KernelTower Λ n)
    (f : Sample Ω S → ℝ) (g : Sample Λ S → ℝ) :
    (S.sampleLaw (KernelTower.prod n T U)).expect
      (fun x => f (sampleFst S x) * g (sampleSnd S x)) =
        (S.sampleLaw T).expect f * (S.sampleLaw U).expect g := by
  rw [sampleExpect_prod]
  simp only [sampleFst_pair,sampleSnd_pair,FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_right]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteAnalytic
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω X : Type} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {x : X} {smooth : WithTop ℕ∞}

lemma contDiffAt_expect (P : FiniteLaw Ω) {f : X → Ω → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) :
    ContDiffAt ℝ smooth (fun x => P.expect (f x)) x := by
  apply ContDiffAt.sum
  intro a _
  exact contDiffAt_const.mul (hf a)

lemma contDiffAt_expMoment (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) :
    ContDiffAt ℝ smooth (fun x => P.expMoment m (f x)) x :=
  P.contDiffAt_expect (fun a => (contDiffAt_const.mul (hf a)).exp)

lemma contDiffAt_logMean (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) :
    ContDiffAt ℝ smooth (fun x => P.logMean m (f x)) x := by
  exact ((P.contDiffAt_expMoment m hf).log (P.expMoment_pos m (f x)).ne').div_const m

lemma contDiffAt_tilt_weight (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) (a : Ω) :
    ContDiffAt ℝ smooth (fun x => (P.tilt m (f x)).weight a) x := by
  exact (contDiffAt_const.mul (contDiffAt_const.mul (hf a)).exp).div
    (P.contDiffAt_expMoment m hf) (P.expMoment_pos m (f x)).ne'
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {x : X} {smooth : WithTop ℕ∞}
lemma contDiffAt_backwardLog (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ a, ContDiffAt ℝ smooth (fun x => f x a) x) :
    ContDiffAt ℝ smooth (fun x => backwardLog n T m (f x)) x := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact T.1.contDiffAt_logMean (m 0)
      (fun a => ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)))
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω X : Type} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {x : X} {smooth : WithTop ℕ∞}
lemma contDiffAt_tilt_sample_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ y, ContDiffAt ℝ smooth (fun x => f x y) x) (a : S.Sample Ω) :
    ContDiffAt ℝ smooth (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).weight a) x := by
  induction S with
  | leaf => exact contDiffAt_const
  | @node n k C ih =>
    change ContDiffAt ℝ smooth (fun x => ∏ i : Fin k,
      (T.1.tilt (m 0) (fun z => KernelTower.backwardLog n (T.2 z)
        (fun j => m j.succ) (fun y => f x (z,y)))).weight (a i).1 *
      ((C i).sampleLaw (KernelTower.tilt n (T.2 (a i).1)
        (fun j => m j.succ) (fun y => f x ((a i).1,y)))).weight (a i).2) x
    apply contDiffAt_prod
    intro i _
    exact (T.1.contDiffAt_tilt_weight (m 0)
      (fun z => KernelTower.contDiffAt_backwardLog n (T.2 z) (fun j => m j.succ)
        (fun y => hf (z,y))) (a i).1).mul
      (ih i (T.2 (a i).1) (fun j => m j.succ) (fun y => hf ((a i).1,y)) (a i).2)

lemma contDiffAt_tilt_sample_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    {g : X → S.Sample Ω → ℝ}
    (hf : ∀ y, ContDiffAt ℝ smooth (fun x => f x y) x)
    (hg : ∀ a, ContDiffAt ℝ smooth (fun x => g x a) x) :
    ContDiffAt ℝ smooth (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).expect (g x)) x := by
  apply ContDiffAt.sum
  intro a _
  exact (contDiffAt_tilt_sample_weight S T m hf a).mul (hg a)
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeMarkLaw
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

variable {Ω : Type}

variable [Fintype Ω]

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.treeMarkLawEdgeDecidableEq
/-- Under the genuine independent mark prior, vertex marks have the product
law at their actual depths. This is a law statement, not a coupling assumption. -/
lemma sampleLaw_markPrior_weight {n : ℕ} (S : PrescribedTree n)
    (Q : Fin n → FiniteLaw Ω) (x : Sample Ω S) :
    (S.sampleLaw (markPrior n Q)).weight x =
      ∏ e : Edge S, (Q (edgeDepth S e)).weight (vertexValues S x e) := by
  classical
  induction S with
  | leaf =>
    change 1 = ∏ e : Empty, (Q (edgeDepth .leaf e)).weight (vertexValues .leaf x e)
    simp
  | @node n k C ih =>
    change (∏ i, (Q 0).weight (x i).1 *
      ((C i).sampleLaw (markPrior n (fun j => Q j.succ))).weight (x i).2) = _
    change _ = ∏ e : ((i : Fin k) × Option (Edge (C i))),
      (Q (edgeDepth (.node k C) e)).weight (vertexValues (.node k C) x e)
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fintype.prod_option,ih]
    rfl

lemma expect_markPrior {n : ℕ} (S : PrescribedTree n)
    (Q : Fin n → FiniteLaw Ω) (f : Sample Ω S → ℝ) :
    (S.sampleLaw (markPrior n Q)).expect f =
      (FiniteLaw.pi (fun e : Edge S => Q (edgeDepth S e))).expect
        (fun v => f (ofVertexValues S v)) := by
  classical
  unfold FiniteLaw.expect
  exact Fintype.sum_equiv (vertexEquiv S) _ _ (fun x => by
    simp only [vertexEquiv,Equiv.coe_fn_mk,of_vertexValues,FiniteLaw.pi,sampleLaw_markPrior_weight])

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

noncomputable local instance treeMarkLawPropDecidable_r802ef5_1 (proposition : Prop) :
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ColoredAnchor
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

lemma hasDerivAt_protectedAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (G : Sample Ω S → ℝ) {A : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, 0 < A u y) (hdA : ∀ y, HasDerivAt (fun t => A t y) (D y) u) :
    HasDerivAt (fun t => protectedAt S T m G (A t))
      (∑ v : Internal S, gamma S m v * protectedAt (grow S v) T m
        (fun x => G (oldSample S v x) * D (newPath S v x)) (A u)) u := by
  classical
  let f (t : ℝ) (y : FinitePath Ω n) := Real.log (A t y)
  let DL (y : FinitePath Ω n) := D y / A u y
  let T' := KernelTower.tilt n T (fun j => m j.succ) (f u)
  have hf (y : FinitePath Ω n) : HasDerivAt (fun t => f t y) (DL y) u :=
    (hdA y).log (hA y).ne'
  have hd := protected_leaf_extension_rule S T m hm hroot hend Finset.univ G hf
  have hfun : (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G x * Real.exp (-protectedLog S Finset.univ (f t) x))) =
      (fun t => protectedAt S T m G (A t)) := by
    funext t
    apply FiniteLaw.expect_congr
    intro x
    rw [leafSum_eq_sum]
    rfl
  rw [hfun] at hd
  apply hd.congr_deriv
  simp only [Finset.sdiff_self, Finset.sum_empty, zero_add]
  have hsum : (sampleLaw S T').expect (fun x =>
      (G x * Real.exp (-protectedLog S Finset.univ (f u) x)) *
      ∑ v : Internal S, gamma S m v * freshEval S T' v DL x) =
      ∑ v : Internal S, gamma S m v *
        (sampleLaw S T').expect (fun x =>
          (G x * Real.exp (-leafSum S (f u) x)) * freshEval S T' v DL x) := by
    simp only [Finset.mul_sum, FiniteLaw.expect_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [← FiniteLaw.expect_mul_left]
    apply FiniteLaw.expect_congr
    intro x
    rw [leafSum_eq_sum]
    change (G x * Real.exp (-∑ a, f u (pathAt S a x))) *
      (gamma S m v * freshEval S T' v DL x) = _
    ring
  refine hsum.trans (Finset.sum_congr rfl ?_)
  intro v _
  apply congrArg (gamma S m v * ·)
  rw [← extension_sampling S T' v (fun x => G x * Real.exp (-leafSum S (f u) x)) DL]
  apply FiniteLaw.expect_congr
  intro x
  change (G (oldSample S v x) * Real.exp (-leafSum S (f u) (oldSample S v x))) *
    (D (newPath S v x) / A u (newPath S v x)) =
    (G (oldSample S v x) * D (newPath S v x)) * Real.exp (-leafSum (grow S v) (f u) x)
  rw [leafSum_grow, neg_add, Real.exp_add]
  change _ = _ * (Real.exp (-leafSum S (f u) (oldSample S v x)) *
    Real.exp (-Real.log (A u (newPath S v x))))
  rw [Real.exp_neg (Real.log (A u (newPath S v x))), Real.exp_log (hA _)]
  ring

lemma hasDerivAt_protectedAt_varying {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {G : ℝ → Sample Ω S → ℝ} {G' : Sample Ω S → ℝ}
    {A : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, 0 < A u y) (hdA : ∀ y, HasDerivAt (fun t => A t y) (D y) u)
    (hG : ∀ x, HasDerivAt (fun t => G t x) (G' x) u) :
    HasDerivAt (fun t => protectedAt S T m (G t) (A t))
      (protectedAt S T m G' (A u) +
       ∑ v : Internal S, gamma S m v * protectedAt (grow S v) T m
        (fun x => G u (oldSample S v x) * D (newPath S v x)) (A u)) u := by
  let f t y := Real.log (A t y)
  let DL y := D y / A u y
  have hf y : HasDerivAt (fun t => f t y) (DL y) u := (hdA y).log (hA y).ne'
  have hproto := hasDerivAt_protected_expect S T m hm hroot Finset.univ (G u) hf
  have hvar := hasDerivAt_protected_expect_varying S T m hm hroot Finset.univ hf hG
  have hfull := hasDerivAt_protectedAt S T m hm hroot hend (G u) hA hdA
  have heq (H : Sample Ω S → ℝ) (t : ℝ) :
      (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
        (fun x => H x * Real.exp (-protectedLog S Finset.univ (f t) x)) =
        protectedAt S T m H (A t) := by
    apply FiniteLaw.expect_congr
    intro x
    rw [leafSum_eq_sum]
    rfl
  simp_rw [heq] at hproto hvar
  rw [hproto.unique hfull] at hvar
  exact hvar

lemma protectedAt_sum {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) {ι : Type} (U : Finset ι)
    (G : ι → Sample Ω S → ℝ) (A : FinitePath Ω n → ℝ) :
    protectedAt S T m (fun x => ∑ i ∈ U, G i x) A = ∑ i ∈ U, protectedAt S T m (G i) A := by
  unfold protectedAt
  simp only [Finset.sum_mul, FiniteLaw.expect_sum]

lemma hasDerivAt_anchorAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, 0 < A u y) (hdA : ∀ y, HasDerivAt (fun t => A t y) (D y) u) :
    HasDerivAt (fun t => anchorAt S T m U paths G (A t))
      ((∑ i ∈ U, anchorAt S T m (U.erase i) paths (fun x => G x * D (paths i x)) (A u)) +
       ∑ v : Internal S, gamma S m v * anchorAt (grow S v) T m U
        (fun i x => paths i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) (A u)) u := by
  have hprod (x : Sample Ω S) :
      HasDerivAt (fun t : ℝ => G x * ∏ i ∈ U, A t (paths i x))
        (∑ i ∈ U, (G x * D (paths i x)) * ∏ j ∈ U.erase i, A u (paths j x)) u := by
    have hh := (HasDerivAt.fun_finsetProd (u := U) (fun i _ => hdA (paths i x))).const_mul (G x)
    apply hh.congr_deriv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_eq_mul]
    ring
  have hd := hasDerivAt_protectedAt_varying S T m hm hroot hend hA hdA hprod
  apply hd.congr_deriv
  rw [protectedAt_sum]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro v _
    apply congrArg (gamma S m v * ·)
    apply FiniteLaw.expect_congr
    intro x
    change ((G (oldSample S v x) * ∏ i ∈ U, A u (paths i (oldSample S v x))) *
      D (newPath S v x)) * _ = _
    ring

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass

namespace PrescribedTree

lemma coordinate_pathAt {Ω : Type} {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (x : Sample Ω S) (i : Fin n) :
    pathCoordinate n (S.pathAt a x) i = vertexValues S x (leafEdge S a i) := by
  induction S with
  | leaf => exact Fin.elim0 i
  | node k C ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih a.1 a.2 (x a.1).2 j

/-- Sharing the actual depth-(i+1) vertex is exactly the split-depth inequality.
Equality of sampled spin/mark values plays no role in this fact. -/
lemma leafEdge_eq_iff {n : ℕ} (S : PrescribedTree n) (a b : S.Leaf) (i : Fin n) :
    leafEdge S a i = leafEdge S b i ↔ i.val+1 ≤ splitDepth S a b := by
  induction S with
  | leaf => exact Fin.elim0 i
  | @node n k C ih =>
    obtain ⟨a,x⟩ := a
    obtain ⟨b,y⟩ := b
    by_cases h : a = b
    · subst b
      refine Fin.cases ?_ (fun j => ?_) i
      · change (Sigma.mk a none : (a : Fin k) × Option (Edge (C a))) = ⟨a,none⟩ ↔
          1 ≤ splitDepth (.node k C) ⟨a,x⟩ ⟨a,y⟩
        rw [splitDepth_same_child]
        simp
      · change (Sigma.mk a (some (leafEdge (C a) x j)) : (a : Fin k) × Option (Edge (C a))) =
          ⟨a,some (leafEdge (C a) y j)⟩ ↔ j.val+1+1 ≤ splitDepth (.node k C) ⟨a,x⟩ ⟨a,y⟩
        rw [splitDepth_same_child]
        simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,Option.some.injEq,ih]
        omega
    · have he : ∀ j : Fin (n+1), (leafEdge (.node k C) ⟨a,x⟩ j).1 = a := by
        intro j
        exact Fin.cases rfl (fun _ => rfl) j
      have hf : ∀ j : Fin (n+1), (leafEdge (.node k C) ⟨b,y⟩ j).1 = b := by
        intro j
        exact Fin.cases rfl (fun _ => rfl) j
      have hne : leafEdge (.node k C) ⟨a,x⟩ i ≠ leafEdge (.node k C) ⟨b,y⟩ i := by
        intro hh
        exact h (by simpa only [he,hf] using congrArg Sigma.fst hh)
      rw [splitDepth_diff_child C a b h]
      simp only [hne,false_iff]
      omega

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualTreeSelector
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

lemma expect_pi_comm {V R Ω : Type*} [Fintype V] [Fintype R] [Fintype Ω]
    [DecidableEq V] [DecidableEq R] (P : V → R → FiniteLaw Ω)
    (f : (V → R → Ω) → ℝ) :
    (pi (fun v => pi (P v))).expect f =
      (pi (fun r => pi (fun v => P v r))).expect (fun x => f (fun v r => x r v)) := by
  unfold expect
  apply Fintype.sum_equiv (Equiv.piComm (fun (_ : V) (_ : R) => Ω))
  intro x
  change (∏ v, ∏ r, (P v r).weight (x v r)) * f x =
    (∏ r, ∏ v, (P v r).weight (x v r)) * f x
  rw [Finset.prod_comm]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
open MarkSelector


noncomputable local instance instDecidableEqEdge_r802ef5_1 {n : ℕ} (S : PrescribedTree n) : DecidableEq (Edge S) := Classical.decEq _
theorem actual_tree_selector {C R : Type} [Fintype C] [DecidableEq C]
    [Fintype R] [DecidableEq R] {n : ℕ} (S : PrescribedTree n)
    (a b : R → C) (d : R → Fin n) (pos : C → S.Leaf) :
    (S.sampleLaw (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => rademacher)))).expect
      (fun x => ∏ c, pathColor a b d c (S.pathAt (pos c) x)) =
        ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0 := by
  have he (x : Sample (R → Bool) S) :
      (∏ c, pathColor a b d c (S.pathAt (pos c) x)) =
      ∏ r, sign (pathCoordinate n (S.pathAt (pos (a r)) x) (d r) r) *
        sign (pathCoordinate n (S.pathAt (pos (b r)) x) (d r) r) := by
    simp only [pathColor]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro r _
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]
  simp_rw [he]
  rw [expect_markPrior]
  simp_rw [coordinate_pathAt,vertexValues_of]
  rw [FiniteLaw.expect_pi_comm]
  rw [MarkSelector.requirements_selector]
  apply Finset.prod_congr rfl
  intro r _
  simp only [leafEdge_eq_iff]

/-- The same selector after adjoining the fresh mark prior to ANY previous
physical reservoir, including its complete existing mark alphabet and tilt. -/
theorem actual_tree_selector_prod {Ω C R : Type} [Fintype Ω]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : R → C) (d : R → Fin n) (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    (S.sampleLaw (KernelTower.prod n T
      (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => rademacher))))).expect
      (fun x => f (sampleFst S x) * ∏ c, pathColor a b d c
        (KernelTower.pathSnd n (S.pathAt (pos c) x))) =
      (S.sampleLaw T).expect f *
        ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0 := by
  simp_rw [← pathAt_sampleSnd]
  rw [expect_prod_separated S T _ f (fun x => ∏ c, pathColor a b d c (S.pathAt (pos c) x)),
    actual_tree_selector]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ColorIterate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped ContDiff

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

lemma contDiffAt_anchorAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) {ι : Type} (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) :
    ContDiffAt ℝ ω (anchorAt S T m U paths G) A := by
  apply contDiffAt_tilt_sample_expect
  · intro y
    exact (contDiffAt_apply ℝ ℝ y A).log (hA y).ne'
  · intro x
    apply ContDiffAt.mul
    · apply contDiffAt_const.mul
      exact contDiffAt_prod (fun i _ => contDiffAt_apply ℝ ℝ (paths i x) A)
    · apply ContDiffAt.exp
      apply ContDiffAt.neg
      simp only [leafSum_eq_sum]
      apply ContDiffAt.sum
      intro a _
      exact (contDiffAt_apply ℝ ℝ (pathAt S a x) A).log (hA _).ne'

lemma contDiffAt_coloredAt {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    {ι : Type} [DecidableEq ι] (ds : List (FinitePath Ω n → ℝ))
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) :
    ContDiffAt ℝ ω (coloredAt T m ds S U paths G) A := by
  induction ds generalizing S U with
  | nil => exact contDiffAt_anchorAt S T m U paths G hA
  | cons D ds ih =>
    apply ContDiffAt.add
    · exact ContDiffAt.sum (fun i _ => ih S (U.erase i) paths (fun x => G x * D (paths i x)))
    · exact ContDiffAt.sum (fun v _ => contDiffAt_const.mul
        (ih (grow S v) U (fun i x => paths i (oldSample S v x))
          (fun x => G (oldSample S v x) * D (newPath S v x))))

/-- Differentiating a colored history inserts the next color at the end of
the ordered history. No symmetrization is imposed as a definition. -/
lemma hasDerivAt_coloredAt {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (ds : List (FinitePath Ω n → ℝ))
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, 0 < A u y) (hdA : ∀ y, HasDerivAt (fun t => A t y) (D y) u) :
    HasDerivAt (fun t => coloredAt T m ds S U paths G (A t))
      (coloredAt T m (ds ++ [D]) S U paths G (A u)) u := by
  induction ds generalizing S U with
  | nil => exact hasDerivAt_anchorAt S T m hm hroot hend U paths G hA hdA
  | cons E ds ih =>
    have h₁ := HasDerivAt.fun_sum (u := U) (fun i _ => ih S (U.erase i) paths
      (fun x => G x * E (paths i x)))
    have h₂ := HasDerivAt.fun_sum (u := Finset.univ) (fun v _ => (ih (grow S v) U
        (fun i x => paths i (oldSample S v x))
        (fun x => G (oldSample S v x) * E (newPath S v x))).const_mul (gamma S m v))
    apply (h₁.add h₂).congr_of_eventuallyEq
    filter_upwards [] with parameter
    rfl

lemma fderiv_coloredAt_apply {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (ds : List (FinitePath Ω n → ℝ))
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) (D : FinitePath Ω n → ℝ) :
    fderiv ℝ (coloredAt T m ds S U paths G) A D =
      coloredAt T m (ds ++ [D]) S U paths G A := by
  have hF : DifferentiableAt ℝ (coloredAt T m ds S U paths G) A :=
    (contDiffAt_coloredAt T m ds S U paths G hA).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => A + t • D) D 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add A
  have hF' : HasFDerivAt (coloredAt T m ds S U paths G)
      (fderiv ℝ (coloredAt T m ds S U paths G) A) (A + (0 : ℝ) • D) := by
    simpa using hF.hasFDerivAt
  have hcomp := hF'.comp_hasDerivAt 0 hline
  have hd := hasDerivAt_coloredAt T m hm hroot hend ds S U paths G
    (A := fun t y => A y + t * D y) (D := D) (u := 0) (by simpa using hA)
    (fun y => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (D y)).const_add (A y))
  simpa using hcomp.unique hd

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ColorSymmetry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped ContDiff

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

lemma eventually_positive_insertion {n : ℕ} {A : FinitePath Ω n → ℝ}
    (hA : ∀ y, 0 < A y) : ∀ᶠ B in nhds A, ∀ y, 0 < B y := by
  rw [Filter.eventually_all]
  intro y
  exact (isOpen_lt continuous_const (continuous_apply y)).mem_nhds (hA y)

/-- The actual iterated Fréchet derivative is the ordered colored expansion.
The reverse only records the outermost-first convention of iteratedFDeriv. -/
lemma iteratedFDeriv_anchorAt {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (k : ℕ)
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) (ds : Fin k → FinitePath Ω n → ℝ) :
    iteratedFDeriv ℝ k (anchorAt S T m U paths G) A ds =
      coloredAt T m (List.ofFn ds).reverse S U paths G A := by
  induction k generalizing A with
  | zero => simp [coloredAt]
  | succ k ih =>
    have hh := (contDiffAt_anchorAt S T m U paths G hA).differentiableAt_iteratedFDeriv
      (m := k) (by simp)
    rw [hh.iteratedFDeriv_succ_apply_left']
    have heq : (fun B => iteratedFDeriv ℝ k (anchorAt S T m U paths G) B (Fin.tail ds))
        =ᶠ[nhds A] (fun B => coloredAt T m (List.ofFn (Fin.tail ds)).reverse S U paths G B) := by
      filter_upwards [eventually_positive_insertion hA] with B hB
      exact ih hB (Fin.tail ds)
    rw [heq.fderiv_eq, fderiv_coloredAt_apply T m hm hroot hend _ S U paths G hA]
    rw [List.ofFn_succ, List.reverse_cons]
    rfl

lemma coloredAt_replicate {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    {ι : Type} [DecidableEq ι] (k : ℕ) (D : FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ) (t : ℝ) :
    coloredAt T m (List.replicate k D) S U paths G (fun y => 1+t*D y) =
      anchorIterate T m D k S U paths G t := by
  induction k generalizing S U with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, coloredAt, anchorIterate, ih]

lemma iteratedFDeriv_anchorAt_diagonal {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (k : ℕ) (D : FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ) :
    iteratedFDeriv ℝ k (anchorAt S T m U paths G) (fun _ => 1) (fun _ => D) =
      anchorIterate T m D k S U paths G 0 := by
  rw [iteratedFDeriv_anchorAt T m hm hroot hend k S U paths G (by simp)]
  simpa using coloredAt_replicate T m k D S U paths G 0

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Polarization
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace DilutedSpinGlass.Polarization

variable {ι : Type} [DecidableEq ι]

lemma flip_involutive (j : ι) : Function.Involutive (flip j) := by
  intro ε
  funext i
  by_cases h : i=j <;> simp [flip, h]

variable [Fintype ι]

lemma prod_sign_flip (j : ι) (ε : ι → Bool) :
    (∏ i, sign (flip j ε i)) = -(∏ i, sign (ε i)) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => sign (flip j ε i)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ (fun i => sign (ε i)) (Finset.mem_univ j)]
  simp only [flip, Function.update_self, sign_not, neg_mul]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- The signed cube average annihilates every non-surjective assignment of
k slots to k colors. Thus only permutations survive polarization. -/
lemma signed_cube_sum (f : ι → ι) :
    (∑ ε : ι → Bool, (∏ i, sign (ε i)) * ∏ i, sign (ε (f i))) =
      if Function.Bijective f then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  by_cases hf : Function.Bijective f
  · rw [ite_eq_left hf]
    have he (ε : ι → Bool) : (∏ i, sign (ε (f i))) = ∏ i, sign (ε i) :=
      Equiv.prod_comp (Equiv.ofBijective f hf) (fun i => sign (ε i))
    simp_rw [he, ← Finset.prod_mul_distrib, sign_sq]
    simp
  · rw [ite_eq_right hf]
    have hns : ¬ Function.Surjective f := fun hs => hf ⟨(Finite.injective_iff_surjective).mpr hs, hs⟩
    obtain ⟨j, hj⟩ : ∃ j, ∀ i, f i ≠ j := by simpa [Function.Surjective] using hns
    let H (ε : ι → Bool) := (∏ i, sign (ε i)) * ∏ i, sign (ε (f i))
    have hflip (ε : ι → Bool) : H (flip j ε) = -H ε := by
      dsimp [H]
      rw [prod_sign_flip]
      have he : (∏ i, sign (flip j ε (f i))) = ∏ i, sign (ε (f i)) := by
        apply Finset.prod_congr rfl
        intro i _
        simp [flip, hj i]
      rw [he, neg_mul]
    have he := Equiv.sum_comp (Equiv.ofBijective (flip j) (flip_involutive j).bijective) H
    change (∑ ε, H (flip j ε)) = ∑ ε, H ε at he
    simp_rw [hflip, Finset.sum_neg_distrib] at he
    change (∑ ε, H ε) = 0
    linarith

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- Unnormalized real polarization, with exactly the ordered-permutation
multiplicity. This does not assume a vanishing diagonal. -/
lemma signed_polarization (M : MultilinearMap ℝ (fun _ : ι => E) ℝ)
    (hsym : ∀ (v : ι → E) (π : Equiv.Perm ι), M (v ∘ π) = M v) (v : ι → E) :
    (∑ ε : ι → Bool, (∏ j, sign (ε j)) *
        M (fun _ => ∑ j, sign (ε j) • v j)) =
      (2 : ℝ) ^ Fintype.card ι * (Fintype.card ι).factorial * M v := by
  classical
  have he (ε : ι → Bool) : M (fun _ : ι => ∑ j, sign (ε j) • v j) =
      ∑ f : ι → ι, (∏ i, sign (ε (f i))) * M (fun i => v (f i)) := by
    rw [M.map_sum]
    apply Finset.sum_congr rfl
    intro f _
    simpa only [smul_eq_mul] using M.map_smul_univ (fun i => sign (ε (f i))) (fun i => v (f i))
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, signed_cube_sum]
  have hc : (Finset.univ.filter (Function.Bijective : (ι → ι) → Prop)).card =
      (Fintype.card ι).factorial := by
    calc
      _ = Fintype.card {f : ι → ι // Function.Bijective f} := (Fintype.card_subtype _).symm
      _ = Fintype.card (Equiv.Perm ι) := Fintype.card_congr Equiv.bijectiveEquiv
      _ = _ := Fintype.card_perm
  calc
    _ = ∑ f ∈ Finset.univ.filter (Function.Bijective : (ι → ι) → Prop), (2 : ℝ) ^ Fintype.card ι * M v := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : Function.Bijective f
      · simp only [ite_eq_left hf]
        apply congrArg ((2 : ℝ) ^ Fintype.card ι * ·)
        exact hsym v (Equiv.ofBijective f hf)
      · simp only [ite_eq_right hf, zero_mul]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hc]; ring


lemma normalized_polarization {k : ℕ} (hk : 0 < k)
    (M : MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (hsym : ∀ (v : Fin k → E) (π : Equiv.Perm (Fin k)), M (v ∘ π) = M v)
    (v : Fin k → E) :
    M v = ((k : ℝ)^k / (2^k * k.factorial)) *
      ∑ ε : Fin k → Bool, (∏ j, sign (ε j)) * M (fun _ => averageDirection ε v) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hscale (ε : Fin k → Bool) :
      (k : ℝ)^k * M (fun _ => averageDirection ε v) =
        M (fun _ => ∑ j, sign (ε j) • v j) := by
    unfold averageDirection
    rw [M.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hk0, one_pow, one_mul]
  have he := signed_polarization M hsym v
  simp only [Fintype.card_fin] at he
  simp_rw [← hscale] at he
  have hh : (k : ℝ)^k *
      (∑ ε : Fin k → Bool, (∏ j, sign (ε j)) * M (fun _ => averageDirection ε v)) =
      (2^k * (k.factorial : ℝ)) * M v := by
    rw [Finset.mul_sum]
    convert he using 1
    · apply Finset.sum_congr rfl
      intro ε _
      ring
  have hd : (2^k * (k.factorial : ℝ)) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero k)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hd).mpr
  linarith

end DilutedSpinGlass.Polarization
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ColorPolarization
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped ContDiff BigOperators

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

 
theorem coloredAt_polarization {n k : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (hk : 0 < k) {ι : Type} [DecidableEq ι]
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    (ds : Fin k → FinitePath Ω n → ℝ) :
    coloredAt T m (List.ofFn ds).reverse S U paths G (fun _ => 1) =
      ((k : ℝ)^k / (2^k * k.factorial)) *
      ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        anchorIterate T m (Polarization.averageDirection ε ds) k S U paths G 0 := by
  rw [← iteratedFDeriv_anchorAt T m hm hroot hend k S U paths G (by simp)]
  have hsym := fun (v : Fin k → FinitePath Ω n → ℝ) (π : Equiv.Perm (Fin k)) => (contDiffAt_anchorAt S T m U paths G (A := fun _ => 1)
    (by simp)).iteratedFDeriv_comp_perm v π
  have hp := Polarization.normalized_polarization hk
    (iteratedFDeriv ℝ k (anchorAt S T m U paths G) (fun _ => 1)).toMultilinearMap hsym ds
  change iteratedFDeriv ℝ k (anchorAt S T m U paths G) (fun _ => 1) ds = _ at hp
  rw [hp]
  apply congrArg (((k : ℝ)^k / (2^k * k.factorial)) * ·)
  apply Finset.sum_congr rfl
  intro ε _
  apply congrArg ((∏ j, Polarization.sign (ε j)) * ·)
  exact iteratedFDeriv_anchorAt_diagonal T m hm hroot hend k
    (Polarization.averageDirection ε ds) S U paths G

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeSampleProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type}

/-- The paths at all leaf positions determine the entire sample. -/
lemma sample_ext {n : ℕ} (S : PrescribedTree n) {x y : Sample Ω S}
    (h : ∀ a : S.Leaf, S.pathAt a x = S.pathAt a y) : x = y := by
  induction S with
  | leaf => exact @Subsingleton.elim Unit inferInstance x y
  | @node n k C ih =>
    funext i
    apply Prod.ext
    · exact congrArg (fun z : FinitePath Ω (n+1) => z.1) (h ⟨i,firstLeaf (C i)⟩)
    · apply ih i
      intro a
      exact congrArg (fun z : FinitePath Ω (n+1) => z.2) (h ⟨i,a⟩)

lemma sampleFst_oldSample {n : ℕ} (S : PrescribedTree n) (v : S.Internal)
    (x : Sample (Ω×Λ) (grow S v)) :
    sampleFst S (oldSample S v x) = oldSample S v (sampleFst (grow S v) x) := by
  apply sample_ext S
  intro a
  calc
    _ = KernelTower.pathFst n (S.pathAt a (oldSample S v x)) := pathAt_sampleFst S a _
    _ = KernelTower.pathFst n ((grow S v).pathAt (oldLeaf S v a) x) := by rw [pathAt_oldLeaf]
    _ = (grow S v).pathAt (oldLeaf S v a) (sampleFst (grow S v) x) := (pathAt_sampleFst _ _ _).symm
    _ = _ := pathAt_oldLeaf _ _ _ _

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeEmbedding
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

end SplitMap
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_LabeledColorHistory
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
variable {Ω : Type} [Fintype Ω]

lemma anchorAt_one {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    {ι : Type} (U : Finset ι) (paths : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) :
    anchorAt S T m U paths G (fun _ => 1) = (sampleLaw S T).expect G := by
  have h := anchorEval_zero S T m hm (fun _ => 0) U paths G
  simpa only [anchorEval,fullyProtected,anchorAt,protectedAt,mul_zero,add_zero,zero_mul] using h

/-- The genuine mixed derivative has precisely the signed labeled-history
expansion. No factorial, unsigned normalization, or law is substituted. -/
theorem coloredAt_labeledHistory {n : ℕ} {C ι : Type} [Fintype C]
    [DecidableEq C] [DecidableEq ι] (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : C → FinitePath Ω n → ℝ) (cs : List C) (hcs : cs.Nodup)
    (P : Finset C) (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    coloredAt T m (cs.map D) S U (fun i => S.pathAt (loc i))
      (fun x => f x * ∏ c ∈ P, D c (S.pathAt (pos c) x)) (fun _ => 1) =
    labeledHistory m (fun S pos f => (S.sampleLaw T).expect
      (fun x => f x * ∏ c, D c (S.pathAt (pos c) x))) cs S U loc pos f := by
  induction cs generalizing P S U with
  | nil =>
    have hP : P = Finset.univ := by simpa using hfull
    simp only [List.map_nil,coloredAt,labeledHistory,anchorAt_one S T m hm,hP]
  | cons c cs ih =>
    have hcP : c ∉ P := hdis c (by simp)
    have hc : c ∉ cs := (List.nodup_cons.mp hcs).1
    have hcs' := (List.nodup_cons.mp hcs).2
    have hdis' : ∀ d ∈ cs, d ∉ insert c P := by
      intro d hd
      simp only [Finset.mem_insert,not_or]
      exact ⟨fun he => hc (he ▸ hd), hdis d (by simp [hd])⟩
    have hfull' : insert c P ∪ cs.toFinset = Finset.univ := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hfull
    simp only [List.map_cons,coloredAt,labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have he : (fun x => (f x * ∏ d ∈ P, D d (S.pathAt (pos d) x)) * D c (S.pathAt (loc i) x)) =
          (fun x => f x * ∏ d ∈ insert c P, D d (S.pathAt (Function.update pos c (loc i) d) x)) := by
        funext x
        rw [Finset.prod_insert hcP,Function.update_self]
        have hp : (∏ d ∈ P, D d (S.pathAt (Function.update pos c (loc i) d) x)) =
            ∏ d ∈ P, D d (S.pathAt (pos d) x) := by
          apply Finset.prod_congr rfl
          intro d hd
          rw [Function.update_of_ne (fun h : d = c => hcP (h ▸ hd))]
        rw [hp]
        ring
      rw [he]
      exact ih hcs' (insert c P) hdis' hfull' S (U.erase i) loc
        (Function.update pos c (loc i)) f
    · apply Finset.sum_congr rfl
      intro v _
      apply congrArg (gamma S m v * ·)
      have hp : (fun i (x : Sample Ω (grow S v)) => S.pathAt (loc i) (oldSample S v x)) =
          (fun i => (grow S v).pathAt (oldLeaf S v (loc i))) := by
        funext i x
        exact (pathAt_oldLeaf S v (loc i) x).symm
      have he : (fun x => (f (oldSample S v x) * ∏ d ∈ P,
          D d (S.pathAt (pos d) (oldSample S v x))) * D c (newPath S v x)) =
          (fun x => f (oldSample S v x) * ∏ d ∈ insert c P,
            D d ((grow S v).pathAt
              (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) d) x)) := by
        funext x
        rw [Finset.prod_insert hcP,Function.update_self,pathAt_newLeaf]
        have hh : (∏ d ∈ P, D d ((grow S v).pathAt
            (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) d) x)) =
            ∏ d ∈ P, D d (S.pathAt (pos d) (oldSample S v x)) := by
          apply Finset.prod_congr rfl
          intro d hd
          rw [Function.update_of_ne (fun h : d = c => hcP (h ▸ hd)),pathAt_oldLeaf]
        rw [hh]
        ring
      rw [hp,he]
      exact ih hcs' (insert c P) hdis' hfull' (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x))

end DilutedSpinGlass.PrescribedTree
end

end

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

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ForkTree
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

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

omit [Fintype Ω] in
theorem leafProduct_bound {n : ℕ} (S : PrescribedTree n)
    {f : FinitePath Ω n → ℝ} (hf : ∀ x, |f x| ≤ 1) (z : Sample Ω S) :
    |leafProduct S f z| ≤ 1 := by
  rw [leafProduct_eq_prod,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun a _ => hf (pathAt S a z))

end DilutedSpinGlass.PrescribedTree

end

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


lemma average_eq (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) :
    average D F = (∑ q ∈ Finset.univ.filter D, F q)/(L:ℝ)^(Fintype.card α) := by
  classical
  unfold average depthLaw FiniteLaw.expect FiniteLaw.pi FiniteLaw.uniform
  simp only [Fintype.card_fin,Finset.prod_const,Finset.card_univ]
  rw [← Finset.mul_sum,← Finset.sum_filter]
  rw [inv_pow,div_eq_mul_inv,mul_comm]

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
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_HistorySelector
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
variable {Ω Λ : Type}

/-- Exact transport of the finite history expansion through an old-sample
projection which commutes with deleting the newly grown branch. -/
lemma labeledHistory_projection {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]
    (m : Fin (n+1) → ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample (Ω×Λ) S → ℝ) → ℝ)
    (W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hVW : ∀ S pos f, V S pos (fun x => f (sampleFst S x)) = W S pos f)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m V cs S U loc pos (fun x => f (sampleFst S x)) =
      labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => exact hVW S pos f
  | cons c cs ih =>
    simp only [labeledHistory]
    congr 1
    · exact Finset.sum_congr rfl (fun i hi => ih S (U.erase i) loc (Function.update pos c (loc i)) f)
    · apply Finset.sum_congr rfl
      intro v _
      apply congrArg (gamma S m v * ·)
      simp_rw [sampleFst_oldSample]
      exact ih (grow S v) U (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x))

variable [Fintype Ω]

/-- Mark integration selects the specified sharing constraints, history by
history, without changing any signed coefficients or the old reservoir. -/
theorem labeledHistory_mark_selector {n : ℕ} {C R ι : Type}
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R] [DecidableEq ι]
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (a b : R → C) (d : R → Fin n) (spinColor : C → FinitePath Ω n → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f =>
      (S.sampleLaw (KernelTower.prod n T
        (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher))))).expect
      (fun x => f x * ∏ c, spinColor c (KernelTower.pathFst n (S.pathAt (pos c) x)) *
        MarkSelector.pathColor a b d c (KernelTower.pathSnd n (S.pathAt (pos c) x))))
      cs S U loc pos (fun x => f (sampleFst S x)) =
    labeledHistory m (fun S pos f =>
      (S.sampleLaw T).expect (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x)) *
        ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0)
      cs S U loc pos f := by
  apply labeledHistory_projection
  intro S pos f
  simp_rw [Finset.prod_mul_distrib,← pathAt_sampleFst,← mul_assoc]
  exact actual_tree_selector_prod S T a b d pos
    (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x))

 
theorem coloredAt_mark_selector {n : ℕ} {C R ι : Type}
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R] [DecidableEq ι]
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (a b : R → C) (d : R → Fin n) (spinColor : C → FinitePath Ω n → ℝ)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    let D := fun c (y : FinitePath (Ω × (R→Bool)) n) =>
      spinColor c (KernelTower.pathFst n y) * MarkSelector.pathColor a b d c (KernelTower.pathSnd n y)
    coloredAt (KernelTower.prod n T
        (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher))))
      m (cs.map D) S U (fun i => S.pathAt (loc i))
      (fun x => f (sampleFst S x) * ∏ c ∈ P, D c (S.pathAt (pos c) x)) (fun _ => 1) =
    labeledHistory m (fun S pos f =>
      (S.sampleLaw T).expect (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x)) *
        ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0)
      cs S U loc pos f := by
  dsimp only
  rw [coloredAt_labeledHistory _ m hm _ cs hcs P hdis hfull]
  exact labeledHistory_mark_selector T m a b d spinColor cs S U loc pos f

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

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SelectorPolarization
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
variable {Ω : Type} [Fintype Ω]

/-- Polarization and the actual tree mark selector identify the constrained
history sum with diagonal canceled-anchor coefficients. The factorial cancels
exactly, leaving k^k/2^k times the signed finite sum of Taylor coefficients. -/
theorem constrainedHistory_polarization {n k : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (hk : 0 < k) (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (a b : R → Option (Fin k)) (d : R → Fin n)
    (spinColor : Option (Fin k) → FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (anchor : S.Leaf) (f : Sample Ω S → ℝ) :
    let T' := KernelTower.prod n T (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher)))
    let D := fun c (y : FinitePath (Ω×(R→Bool)) n) =>
      spinColor c (KernelTower.pathFst n y) * MarkSelector.pathColor a b d c (KernelTower.pathSnd n y)
    let G := fun x => f (sampleFst S x) * D none (S.pathAt anchor x)
    constrainedHistory T m a b d spinColor S anchor f =
      ((k:ℝ)^k/2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        anchorCoefficient S T' m (Polarization.averageDirection ε (fun j => D (some j))) anchor G k := by
  classical
  dsimp only
  let D := fun c (y : FinitePath (Ω×(R→Bool)) n) =>
    spinColor c (KernelTower.pathFst n y) * MarkSelector.pathColor a b d c (KernelTower.pathSnd n y)
  let T' := KernelTower.prod n T (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher)))
  let G := fun x => f (sampleFst S x) * D none (S.pathAt anchor x)
  let cs := (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse
  have hcs : cs.Nodup := by
    rw [List.nodup_reverse,List.nodup_ofFn]
    exact Option.some_injective _
  have hdis : ∀ c ∈ cs, c ∉ ({none} : Finset (Option (Fin k))) := by
    intro c hc
    simp only [cs,List.mem_reverse,List.mem_ofFn] at hc
    obtain ⟨j,rfl⟩ := hc
    simp
  have hfull : ({none} : Finset (Option (Fin k))) ∪ cs.toFinset = Finset.univ := by
    ext c
    cases c with
    | none => simp
    | some j => simp [cs,List.mem_ofFn]
  have hsel := coloredAt_mark_selector T m hm a b d spinColor cs hcs {none} hdis hfull
    S (Finset.univ.erase anchor) id (fun _ => anchor) f
  have hmapped : cs.map D = (List.ofFn (fun j => D (some j))).reverse := by simp [cs,Function.comp_def]
  change coloredAt T' m (cs.map D) S (Finset.univ.erase anchor) _ _ _ = _ at hsel
  simp only [Finset.prod_singleton,id_eq] at hsel
  rw [hmapped] at hsel
  rw [← show coloredAt T' m (List.ofFn (fun j => D (some j))).reverse S
      (Finset.univ.erase anchor) (S.pathAt) G (fun _ => 1) =
      constrainedHistory T m a b d spinColor S anchor f from hsel]
  rw [coloredAt_polarization T' m hm hroot hend hk]
  simp only [anchorCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  dsimp only [T',G,D]
  ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PatternComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.BooleanPolynomial
open scoped BigOperators
variable {R : Type} [Fintype R] [DecidableEq R]

lemma interpolation (F : (R → Bool) → ℝ) (y : R → Bool) :
    F y = ∑ x : R → Bool, F x * ∏ r, (if x r then truth (y r) else 1-truth (y r)) := by
  classical
  symm
  rw [Finset.sum_eq_single y]
  · have he : ∏ r, (if y r then truth (y r) else 1-truth (y r)) = (1:ℝ) := by
      apply Finset.prod_eq_one
      intro r _
      cases y r <;> norm_num [truth]
    rw [he,mul_one]
  · intro x _ hxy
    have hx : ∃ r, x r ≠ y r := not_forall.mp (fun h => hxy (funext h))
    obtain ⟨r,hr⟩ := hx
    have he : ∏ j, (if x j then truth (y j) else 1-truth (y j)) = (0:ℝ) := by
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      cases hx : x r <;> cases hy : y r <;> simp_all [truth]
    rw [he,mul_zero]
  · simp

lemma product_expansion (x y : R → Bool) :
    (∏ r, (if x r then truth (y r) else 1-truth (y r))) =
      ∑ s : Finset R, ((∏ r ∈ s, if x r then (1:ℝ) else -1) *
        (∏ r ∈ sᶜ, if x r then (0:ℝ) else 1)) * monomial s y := by
  have he (r : R) : (if x r then truth (y r) else 1-truth (y r)) =
      ((if x r then (1:ℝ) else -1) * truth (y r)) + (if x r then (0:ℝ) else 1) := by
    cases x r <;> simp; ring
  simp_rw [he]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib]
  unfold monomial
  ring

/-- Every predicate of a finite sharing profile is a finite real linear
combination of positive sharing requirements. No endpoint mark is needed. -/
theorem expansion (F : (R → Bool) → ℝ) (y : R → Bool) :
    F y = ∑ s : Finset R, coefficient F s * monomial s y := by
  rw [interpolation F y]
  simp_rw [product_expansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

end DilutedSpinGlass.BooleanPolynomial
end

end

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology

lemma limsup_sqrt_error_bound (a b e : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (ha0 : ∀ n, 0≤a n) (hb1 : ∀ n, b n≤1) (he : Tendsto e atTop (𝓝 0))
    (h : ∀ n, c*a n≤Real.sqrt (b n)+e n) :
    c*limsup a atTop≤Real.sqrt (limsup b atTop) := by
  have hcap (t : ℝ) (ht : 0<t) : c*limsup a atTop≤Real.sqrt (limsup b atTop+t)+t := by
    have hef : ∀ᶠ n in atTop, e n<t := he.eventually (Iio_mem_nhds ht)
    have hbf : ∀ᶠ n in atTop, b n<limsup b atTop+t :=
      eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht)
        (isBoundedUnder_of_eventually_le (Eventually.of_forall hb1))
    have hab : ∀ᶠ n in atTop, a n≤(Real.sqrt (limsup b atTop+t)+t)/c := by
      filter_upwards [hef,hbf] with n hen hbn
      apply (le_div_iff₀ hc).mpr
      rw [mul_comm]
      exact (h n).trans (add_le_add (Real.sqrt_le_sqrt hbn.le) hen.le)
    have hl := limsup_le_of_le
      (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha0).frequently)) hab
    simpa only [mul_comm c] using (le_div_iff₀ hc).mp hl
  have hcont : ContinuousAt (fun t : ℝ => Real.sqrt (limsup b atTop+t)+t) 0 := by fun_prop
  have ht := hcont.continuousWithinAt.tendsto (s := Ioi 0)
  have hh := ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun t ht => hcap t ht))
  simpa using hh

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TripleMarginal
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
variable {Ω : Type} [Fintype Ω] {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

omit [Fintype Ω] in
lemma labeledHistory_add (m : Fin (n+1) → ℝ)
    (V W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f => V S pos f + W S pos f) cs S U loc pos f =
      labeledHistory m V cs S U loc pos f + labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [labeledHistory,ih,mul_add,Finset.sum_add_distrib]
    ring

omit [Fintype Ω] in
lemma labeledHistory_mul_left (m : Fin (n+1) → ℝ) (t : ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f => t * V S pos f) cs S U loc pos f =
      t * labeledHistory m V cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [labeledHistory,ih,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    ring

omit [Fintype Ω] in
lemma labeledHistory_zero (m : Fin (n+1) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun _ _ _ => 0) cs S U loc pos f = 0 := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih => simp only [labeledHistory,ih,mul_zero,Finset.sum_const_zero,add_zero]

omit [Fintype Ω] in
lemma labeledHistory_sum {J : Type} (F : Finset J) (m : Fin (n+1) → ℝ)
    (V : J → (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f => ∑ j ∈ F, V j S pos f) cs S U loc pos f =
      ∑ j ∈ F, labeledHistory m (V j) cs S U loc pos f := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,labeledHistory_zero]
  | @insert j F hj ih => simp only [Finset.sum_insert hj,labeledHistory_add,ih]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HistoryDistinct
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

variable {Ω : Type} [Fintype Ω] [Fintype C]

omit [Fintype Ω] in
/-- A colored history never reuses a position. Thus identities only need to
be proved on terminal tuples of distinct geometric leaves, not sample values. -/
lemma labeledHistory_congr_distinct (m : Fin (n+1) → ℝ)
    (V W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hVW : ∀ S pos f, Function.Injective pos → V S pos f = W S pos f)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (h : HistoryValid S U loc P pos) (f : Sample Ω S → ℝ) :
    labeledHistory m V cs S U loc pos f = labeledHistory m W cs S U loc pos f := by
  induction cs generalizing P S U with
  | nil =>
    apply hVW
    have hp : P = Finset.univ := by simpa using hfull
    exact fun a b e => h.pos_inj (by simp [hp]) (by simp [hp]) e
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hdis' : ∀ d ∈ cs, d ∉ insert c P := by
      intro d hd hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact (List.nodup_cons.mp hcs).1 hd
      · exact hdis d (by simp [hd]) hp
    have hfull' : insert c P ∪ cs.toFinset = Finset.univ := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hfull
    simp only [labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact ih (List.nodup_cons.mp hcs).2 (insert c P) hdis' hfull' S (U.erase i) loc
        (Function.update pos c (loc i)) (h.pick_old hc hi) _
    · apply Finset.sum_congr rfl
      intro v _
      congr 1
      exact ih (List.nodup_cons.mp hcs).2 (insert c P) hdis' hfull' (grow S v) U
        (fun i => oldLeaf S v (loc i)) _ (h.pick_fresh hc v) _

lemma anchorHistory_valid (S : PrescribedTree n) (anchor : S.Leaf) {k : ℕ} :
    HistoryValid S (Finset.univ.erase anchor) id ({none} : Finset (Option (Fin k))) (fun _ => anchor) := by
  refine ⟨Function.injective_id,?_,?_⟩
  · intro a ha b hb _
    simp only [Finset.mem_coe,Finset.mem_singleton] at ha hb
    exact ha.trans hb.symm
  · intro i hi c _
    exact (Finset.mem_erase.mp hi).1

end DilutedSpinGlass.PrescribedTree
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

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {L : ℕ} {C : Type} [Fintype C] [DecidableEq C]

omit [Fintype C] in
lemma splitFromProfile_eq (S : PrescribedTree (L+1)) (pos : C → S.Leaf)
    (hp : Function.Injective pos) (a b : C) :
    splitFromProfile (sharingProfile S pos) a b = splitDepth S (pos a) (pos b) := by
  unfold splitFromProfile
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    have hlt := splitDepth_lt_of_ne S (pos a) (pos b) (fun e => hab (hp e))
    have he : (Finset.univ.filter (fun d : Fin L => sharingProfile S pos (a,b,d))) =
        Finset.univ.filter (fun d : Fin L => d.val < splitDepth S (pos a) (pos b)) := by
      ext d
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,sharingProfile,decide_eq_true_eq]
      omega
    rw [he,Fin.card_filter_val_lt,Nat.min_eq_right (by omega)]

omit [Fintype C] [DecidableEq C] in
lemma monomial_sharing (s : Finset (SharingIndex L C)) (S : PrescribedTree (L+1))
    (pos : C → S.Leaf) :
    BooleanPolynomial.monomial s (sharingProfile S pos) =
      ∏ j : Fin (Fintype.card s),
        if (requirementMap s j).2.2.val+1 ≤
          splitDepth S (pos (requirementMap s j).1) (pos (requirementMap s j).2.1)
        then (1:ℝ) else 0 := by
  classical
  unfold BooleanPolynomial.monomial BooleanPolynomial.truth sharingProfile
  simp only [decide_eq_true_eq]
  rw [← Finset.prod_attach]
  simpa [requirementMap] using (Fintype.equivFin s).prod_comp (fun j =>
    if (requirementMap s j).2.2.val+1 ≤
      splitDepth S (pos (requirementMap s j).1) (pos (requirementMap s j).2.1) then (1:ℝ) else 0)

variable {Ω : Type} [Fintype Ω] {k : ℕ}

/-- Full exact splitting constraints reduce to finitely many sharing
histories, using distinct geometric positions throughout every branch. -/
theorem shapeHistory_expansion (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ)
    (spinColor : Option (Fin k) → FinitePath Ω (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (anchor : S.Leaf) (f : Sample Ω S → ℝ) :
    shapeHistory T m F spinColor S anchor f =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        constrainedHistory T m (fun j => (requirementMap s j).1)
          (fun j => (requirementMap s j).2.1) (fun j => (requirementMap s j).2.2.castSucc)
          spinColor S anchor f := by
  classical
  unfold shapeHistory constrainedHistory
  simp_rw [← labeledHistory_mul_left]
  rw [← labeledHistory_sum]
  apply labeledHistory_congr_distinct (P := ({none} : Finset (Option (Fin k))))
  · intro S pos g hp
    have he : (fun a b => splitDepth S (pos a) (pos b)) = splitFromProfile (sharingProfile S pos) := by
      funext a b
      exact (splitFromProfile_eq S pos hp a b).symm
    rw [he,BooleanPolynomial.expansion (fun y => F (splitFromProfile y)) (sharingProfile S pos)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [monomial_sharing]
    simp only [Fin.val_castSucc]
    ring
  · rw [List.nodup_reverse,List.nodup_ofFn]
    exact Option.some_injective _
  · intro c hc
    simp only [List.mem_reverse,List.mem_ofFn] at hc
    obtain ⟨j,rfl⟩ := hc
    simp
  · ext c
    cases c with
    | none => simp
    | some j => simp [List.mem_ofFn]
  · exact anchorHistory_valid S anchor

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
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixHistoryDecidable_r802ef5_1 (p : Prop) : Decidable p :=
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

noncomputable local instance kappaRegularDecidable_r802ef5_1 (p : Prop) : Decidable p :=
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixNormalization
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
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixNormalizationDecidable_r802ef5_1 (proposition : Prop) :
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

noncomputable local instance weightedMatrixHistoryDecidable_r802ef5_1 (proposition : Prop) :
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

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HistoryRetained
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

noncomputable local instance matrixPairPropDecidable_r802ef5_1 (proposition : Prop) : Decidable proposition :=
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalTaylor
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
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n : ℕ}

/-- Measurability of every coefficient of the actual finite extension
recursion, from measurable old-tree expectations. -/
theorem measurable_anchorIterate_zero (T : Z → KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (hT : ∀ (S : PrescribedTree n) (G : S.Sample Ω → ℝ),
      Measurable (fun z => (S.sampleLaw (T z)).expect G))
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι]
    (k : ℕ) (S : PrescribedTree n) (A : Finset ι)
    (U : ι → S.Sample Ω → FinitePath Ω n) (G : S.Sample Ω → ℝ) :
    Measurable (fun z => anchorIterate (T z) m D k S A U G 0) := by
  induction k generalizing S A with
  | zero => simpa only [anchorIterate,anchorEval_zero S _ m hm] using hT S G
  | succ k ih =>
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun i _ => ih S (A.erase i) U _)
    · exact Finset.measurable_sum _ (fun v _ => (ih (grow S v) A _ _).const_mul _)

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

lemma measurable_externalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (k : ℕ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => externalCoefficient S a T Q m (base z) roots i old D E f k) := by
  unfold externalCoefficient PrescribedTree.anchorCoefficient
  apply Measurable.div_const
  apply PrescribedTree.measurable_anchorIterate_zero _ m hm
  intro S G
  simp_rw [← KernelTower.tilt_prod_fst]
  refine PrescribedTree.measurable_tilt_sample_expect S
    (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) (fun j => m j.succ) ?_ ?_
  · exact fun y => (hb _).add measurable_const
  · exact fun x => measurable_const

variable (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) (hD : ∀ x y, |D x y| ≤ 1) (hE : ∀ x y, |E x y| ≤ 1)

include hmono hpos hroot hend hB hf hD hE in
lemma externalCoefficient_bound (k : ℕ) :
    |externalCoefficient S a T Q m base roots i old D E f k| ≤
      B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) k/(k.factorial:ℝ) := by
  unfold externalCoefficient PrescribedTree.anchorCoefficient
  rw [abs_div,abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial:ℝ))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply PrescribedTree.abs_anchorIterate_le _ m hmono hpos hroot hend _ (fun y => hD _ _) k S _ _ _ hB
  · intro x
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (hf _) (hE _ _) (abs_nonneg _) hB
  · norm_num

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

lemma measurable_rootExternalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (j : ℕ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × I => rootExternalCoefficient S a T Q m base old D E f j z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro i
  dsimp only [rootExternalCoefficient]
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  exact measurable_externalCoefficient S a T Q m hm
    (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) i old (D i) (E i) f j (hb k)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalCoefficientLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
variable {Ω I X Y Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma integrable_rootExternalCoefficient_label
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (label : Z → I) (hl : Measurable label) (k : ℕ) :
    Integrable (fun z : FullRootState Y X I M × Z =>
      rootExternalCoefficient S a T Q m base old D E f k z.1 (label z.2))
      ((fullRootLaw ξ μ ν r s).prod τ) := by
  apply Integrable.of_bound ((measurable_rootExternalCoefficient S a T Q m hm base old D E f k hb).comp
    (measurable_fst.prodMk (hl.comp measurable_snd))).aestronglyMeasurable
    (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) k/(k.factorial:ℝ))
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact externalCoefficient_bound S a T Q m hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) (label z.2) old _ _ f hB hf (hD _) (hE _) k)

end DilutedSpinGlass.HeterogeneousMarks
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
variable {Ω C ι : Type} [Fintype Ω] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixConstantDecidable_r802ef5_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
omit [Fintype Ω] in
lemma labeledHistory_congr_one (m : Fin (n+1) → ℝ)
    (V W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (h : ∀ S pos, V S pos (fun _ => 1) = W S pos (fun _ => 1))
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf) :
    labeledHistory m V cs S U loc pos (fun _ => 1) =
      labeledHistory m W cs S U loc pos (fun _ => 1) := by
  induction cs generalizing S U with
  | nil => exact h S pos
  | cons c cs ih => simp only [labeledHistory,ih]

variable [Fintype C]
/-- The anchor-alone complete matrix history is its exact signed kappa times
the single-target marginal observable. In fact the same identity holds with
any unused old tree, as long as its test is one. -/
theorem weightedMatrixHistory_one (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Bijective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a : C) (cs : List C) (hcs : cs.Nodup) (hdis : ∀ c ∈ cs, c ≠ a)
    (hfull : ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf) (A : (C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)))
      m cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) =
    partialKappa T m (Finset.univ.image q) *
      (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z)) := by
  let B := (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z))
  have he := labeledHistory_congr_one m
    (fun D pos g => if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)) else 0)
    (fun D pos g => B * (if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect g else 0))
    (by
      intro D pos
      split_ifs with h
      · simp only [one_mul,FiniteLaw.expect_const,mul_one]
        exact matrix_paths_expect T D q hq.2 pos h K A
      · exact (mul_zero B).symm)
    cs S (Finset.univ.erase x) id (fun _ => x)
  unfold weightedMatrixHistory
  rw [he,labeledHistory_mul_left]
  rw [show labeledHistory m (fun D pos g => if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect g else 0) cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) =
      matrixHistory T q K m cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) from rfl]
  rw [matrixHistory_normalization T q hq.1 K m hm hp hend cs hcs {a}
    (Finset.singleton_nonempty _) (by simpa only [Finset.mem_singleton] using hdis) hfull
    S (Finset.univ.erase x) id (fun _ => x) (singleton_history_cover S x a)
    (by intro b hb d hd; have hb' := Finset.mem_singleton.mp hb; have hd' := Finset.mem_singleton.mp hd
        subst b; subst d; simp only [splitDepth_self]) (fun _ => 1)]
  simp only [Finset.image_singleton,partialKappa_singleton,div_one,FiniteLaw.expect_const,mul_one]
  exact mul_comm _ _

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

noncomputable local instance matrixEnergyPropDecidable_r802ef5_1 (proposition : Prop) :
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
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

lemma sampleLaw_unary_expect (S : PrescribedTree n) (T : KernelTower Ω (n+1))
    (F : Ω × Sample Ω S → ℝ) :
    ((unary S).sampleLaw T).expect (fun z => F (z 0)) =
      T.1.expect (fun a => (S.sampleLaw (T.2 a)).expect (fun w => F (a,w))) := by
  change (FiniteLaw.pi (fun _ : Fin 1 => T.1.bind (fun a => S.sampleLaw (T.2 a)))).expect
    (fun z => F (z 0)) = _
  rw [FiniteLaw.expect_pi_marginal,FiniteLaw.expect_bind]

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
lemma admissible_lower (S : ReducedTopology) (q : S.Vertex → ℕ) {lo hi : ℕ}
    (h : Admissible S q lo hi) (v : S.Vertex) : lo ≤ q v := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none => exact h.1
    | some v => exact h.1.trans ((Nat.le_succ _).trans (ih v.1 _ (h.2.2 v.1) v.2))

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

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_VertexContinuity
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMatrix
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
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N k : ℕ}

noncomputable local instance shapeMatrixPropDecidable_r802ef5_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype Ω] [DecidableEq C] in
lemma spatialProduct_bound [Fintype Ω] [DecidableEq C]
    (D : C → FinitePath Ω L → Fin N → ℝ)
    (hD : ∀ c x i, |D c x i| ≤ 1) (x : C → FinitePath Ω L) :
    |spatialProduct D x| ≤ 1 := by
  unfold spatialProduct
  simp only [abs_div, Nat.abs_cast]
  have hs : |∑ i : Fin N, ∏ c, D c (x c) i| ≤ (N:ℝ) := by
    calc
      _ ≤ ∑ i : Fin N, |∏ c, D c (x c) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun c _ => hD c _ i))
      _ = _ := by simp
  by_cases hN : N = 0
  · subst N; simp
  · exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr (by simpa using hs)

lemma matrixObservableHistory_sum {ι : Type} (I : Finset ι)
    (T : PrescribedTree L) (q : C → T.Leaf) (K : KernelTower Ω L) (m : Fin (L+1) → ℝ)
    (cs : List C) (S : PrescribedTree L) (a : S.Leaf)
    (A : ι → (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) :
    matrixObservableHistory T q K m cs S a (fun x => ∑ i ∈ I, A i x) f =
      ∑ i ∈ I, matrixObservableHistory T q K m cs S a (A i) f := by
  unfold matrixObservableHistory weightedMatrixHistory
  dsimp only
  rw [← labeledHistory_sum]
  congr 1
  funext R pos g
  split_ifs with h
  · simp only [Finset.mul_sum,FiniteLaw.expect_sum]
  · simp only [Finset.sum_const_zero]

lemma matrixObservableHistory_div
    (T : PrescribedTree L) (q : C → T.Leaf) (K : KernelTower Ω L) (m : Fin (L+1) → ℝ)
    (cs : List C) (S : PrescribedTree L) (a : S.Leaf)
    (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) (c : ℝ) :
    matrixObservableHistory T q K m cs S a (fun x => A x/c) f =
      matrixObservableHistory T q K m cs S a A f/c := by
  unfold matrixObservableHistory weightedMatrixHistory
  rw [div_eq_mul_inv,mul_comm,← labeledHistory_mul_left]
  congr 1
  funext R pos g
  split_ifs with h
  · dsimp only
    simp only [div_eq_mul_inv, mul_comm _ c⁻¹, mul_left_comm _ c⁻¹, FiniteLaw.expect_mul_left]
  · simp only [mul_zero]

lemma shapeHistory_matrix (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (K : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (D : Option (Fin k) → FinitePath Ω (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (f : Sample Ω S → ℝ) :
    shapeHistory K m (matrixSplitTest T q) D S a f =
    matrixObservableHistory T q K m
      (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a
      (fun x => ∏ c, D c (x c)) f := by
  unfold shapeHistory matrixObservableHistory weightedMatrixHistory
  congr 1
  funext R pos g
  unfold matrixSplitTest
  split_ifs <;> simp

/-- Empirical multioverlap and literal full-matrix history commute with the
single shared site average. Old tests may depend on every old sample. -/
theorem matrix_history_spatialProduct (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (K : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (D : Option (Fin k) → FinitePath Ω (L+1) → Fin N → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (f : Sample Ω S → ℝ) :
    matrixObservableHistory T q K m
      (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a (spatialProduct D) f =
      (∑ i : Fin N, shapeHistory K m (matrixSplitTest T q) (fun c x => D c x i) S a f)/(N:ℝ) := by
  unfold spatialProduct
  rw [matrixObservableHistory_div,matrixObservableHistory_sum]
  simp_rw [shapeHistory_matrix]

end DilutedSpinGlass.PrescribedTree
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
-- module Solutions.OAIQ041_DS.DilutedSpin_UniversalDictionary
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators


lemma table_bound {L r : ℕ} (g : Table L r) (y : Fin L → Fin r → Bool) :
    |(g.1 y : ℝ)| ≤ 1 := by exact_mod_cast g.2 y
lemma direction_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |direction q σ y| ≤ 1 := by
  rw [direction,abs_mul]
  have hs : |spin σ| = 1 := by cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _
lemma anchor_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |anchor q σ y| ≤ 1 := by
  rw [anchor,abs_mul]
  have hs : |(if q.2.2.2 then spin σ else 1 : ℝ)| = 1 := by
    split <;> cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _

lemma selector_eq_pathColor {L r : ℕ} {C : Type} [DecidableEq C]
    (a b : Fin r → C) (d : Fin r → Fin L) (c : C)
    (y : FinitePath (Fin r → Bool) (L+1)) :
    ((selector a b d c).1 (interior y) : ℝ) =
      MarkSelector.pathColor a b (fun j => (d j).castSucc) c y := by
  simp only [selector,MarkSelector.pathColor,interior,Rat.cast_prod,Rat.cast_mul]
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> simp

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PrefixProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open scoped BigOperators

lemma cast_average {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (g : Fin k → Table L r) (y : Fin L → Fin r → Bool) :
    ((average hk ε g).1 y : ℝ) = (k:ℝ)⁻¹ * ∑ j, MarkSelector.sign (ε j) * ((g j).1 y : ℝ) := by
  simp only [average, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum, cast_signQ]

lemma polarized_direction {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (σ : Spin) (y : FinitePath (Fin r → Bool) (L+1)) :
    direction (polarizedSpec hk ε a b d spinAnchor) σ y =
      (k:ℝ)⁻¹ * ∑ j, MarkSelector.sign (ε j) *
        (spin σ * MarkSelector.pathColor a b (fun t => (d t).castSucc) (some j) y) := by
  simp only [direction,polarizedSpec,cast_average,selector_eq_pathColor]
  rw [mul_assoc,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma polarized_anchor {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (σ : Spin) (y : FinitePath (Fin r → Bool) (L+1)) :
    anchor (polarizedSpec hk ε a b d spinAnchor) σ y =
      (if spinAnchor then spin σ else 1) *
        MarkSelector.pathColor a b (fun t => (d t).castSucc) none y := by
  change ((selector a b d none).1 (interior y) : ℝ) * (if spinAnchor then spin σ else 1) = _
  rw [selector_eq_pathColor,mul_comm]

/-- Every prescribed sharing history is a finite linear combination of the
literal universal dictionary coefficients, with the same old kernel. -/
theorem universal_constrained_polarization {Ω : Type} [Fintype Ω] {L r k : ℕ}
    (hk : 0 < k) (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (read : FinitePath Ω (L+1) → Spin)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf) (f : PrescribedTree.Sample Ω S → ℝ) :
    PrescribedTree.constrainedHistory T m a b (fun j => (d j).castSucc)
      (fun c x =>
        match c with
        | none => if spinAnchor then spin (read x) else 1
        | some _ => spin (read x)) S anchorLeaf f =
    ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
      PrescribedTree.anchorCoefficient S
        (KernelTower.prod (L+1) T (markPrior (L+1) (prior (polarizedSpec hk ε a b d spinAnchor)))) m
        (fun y => direction (polarizedSpec hk ε a b d spinAnchor)
          (read (KernelTower.pathFst (L+1) y)) (KernelTower.pathSnd (L+1) y)) anchorLeaf
        (fun x => f (PrescribedTree.sampleFst S x) *
          anchor (polarizedSpec hk ε a b d spinAnchor)
            (read (KernelTower.pathFst (L+1) (S.pathAt anchorLeaf x)))
            (KernelTower.pathSnd (L+1) (S.pathAt anchorLeaf x))) k := by
  rw [PrescribedTree.constrainedHistory_polarization hk T m hm hroot hend]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  congr 1
  apply congrArg₂ (fun D G => PrescribedTree.anchorCoefficient S
    (KernelTower.prod (L+1) T (markPrior (L+1) (prior (polarizedSpec hk ε a b d spinAnchor)))) m D anchorLeaf G k)
  · funext y
    erw [polarized_direction]
    simp only [Polarization.averageDirection,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
    rfl
  · funext x
    erw [polarized_anchor]
    rfl

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

omit [Fintype Ω] in
lemma treeOverlap_unary (S : PrescribedTree n) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (z : Sample Ω (unary S)) :
    treeOverlap (unary S) f z=treeOverlap S (fun y => f ((z 0).1,y)) (z 0).2 := by
  simp only [treeOverlap,leafProduct_unary]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MultileafMatrixPointwise
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open HeterogeneousMarks PrescribedTree
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] {L n r k : ℕ}

theorem externalHistory_polarization (hk : 0 < k)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → (Spec L×ℕ)×Z)
    (old : (i : (Spec L×ℕ)×Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) :
    externalHistory S anchorLeaf T m base roots old read v a b d spinAnchor f =
      ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        externalCoefficient S anchorLeaf T (fun i => prior i.1.1) m base roots
          ((polarizedSpec hk ε a b d spinAnchor,0),v) old
          (fun x y => direction (polarizedSpec hk ε a b d spinAnchor) (read v x) y)
          (fun x y => anchor (polarizedSpec hk ε a b d spinAnchor) (read v x) y) f k := by
  unfold externalHistory
  erw [universal_constrained_polarization hk _ m hm hroot hend a b d spinAnchor
    (fun x => read v (physical roots (L+1) x)) S anchorLeaf
    (fun x => f (fun a => physical roots (L+1) (S.pathAt a x)))]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  congr 1
  unfold externalCoefficient
  congr 1
  funext x
  congr 1
  congr 1
  funext a
  rw [pathAt_sampleFst]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootMultileafMatrix
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M r k : ℕ}

omit [MeasurableSpace X] [MeasurableSpace Y] [Countable Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] in
lemma rootHistory_polarization (hk : 0 < k)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) :
    rootHistory S anchorLeaf T m base old read a b d spinAnchor f z v =
      ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        rootExternalCoefficient S anchorLeaf T (fun i => prior i.1.1) m base old
          (fun i x y => direction i.1.1 (read i.2 x) y)
          (fun i x y => anchor i.1.1 (read i.2 x) y) f k z
          ((polarizedSpec hk ε a b d spinAnchor,0),v) := by
  exact externalHistory_polarization hk S anchorLeaf T m hm hroot hend
    (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) old read v a b d spinAnchor f

end DilutedSpinGlass.UniversalDictionary
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
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.conditionalScheduledMeanDepthDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]


lemma average_split (a : α) (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) :
    average D F=(FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
      average (fun rest => D (insertCoordinate a t rest)) (fun rest => F (insertCoordinate a t rest))) := by
  unfold average depthLaw insertCoordinate
  exact FiniteLaw.expect_pi_split _ a _

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FirstSplitSchedule
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

lemma realize_unary_of_later (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d<q v) :
    realize (H+1) d S q=PrescribedTree.unary (realize H (d+1) S q) := by
  cases S with
  | leaf => rfl
  | node k hk C => rw [realize,ite_eq_left (hq none)]

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcreteHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M r k : ℕ}

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)

include hb hm hmono hpos hroot hend hB hf

lemma integrable_rootHistory (hk : 0 < k) :
    Integrable (fun z : FullRootState Y X (Labels L Z) M × Z =>
      rootHistory S anchorLeaf T m base old read a b d spinAnchor f z.1 z.2)
      ((fullRootLaw ξ μ ν rate score).prod τ) := by
  have hi (ε : Fin k → Bool) := integrable_rootExternalCoefficient_label ξ μ ν τ rate score
    S anchorLeaf T (fun i => prior i.1.1) m base old
    (fun i x y => direction i.1.1 (read i.2 x) y)
    (fun i x y => anchor i.1.1 (read i.2 x) y) f hb hm hmono hpos hroot hend hB hf
    (fun _ _ _ => direction_bound _ _ _) (fun _ _ _ => anchor_bound _ _ _)
    (fun v => ((polarizedSpec hk ε a b d spinAnchor,0),v))
    (measurable_const.prodMk measurable_id) k
  simp_rw [rootHistory_polarization hk S anchorLeaf T m hm hroot hend base old read a b d spinAnchor f]
  exact (integrable_finsetSum _ (fun ε _ => (hi ε).const_mul _)).const_mul _

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M n k : ℕ}

omit [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma externalShapeHistory_expansion (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → Labels L Z)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) :
    externalShapeHistory S anchorLeaf T m base roots old read v F spinAnchor f =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        externalHistory S anchorLeaf T m base roots old read v
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f := by
  exact shapeHistory_expansion _ m F _ S anchorLeaf _

omit [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma rootShapeHistory_expansion (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) :
    rootShapeHistory S anchorLeaf T m base old read F spinAnchor f z v =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        rootHistory S anchorLeaf T m base old read
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f z v := by
  exact externalShapeHistory_expansion S anchorLeaf T m (base z.1 z.2.1.1 z.2.1.2)
    (rootArray z.2.2.1 z.2.2.2) old read v F spinAnchor f

end DilutedSpinGlass.UniversalDictionary
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

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullCubeConditionalContinuity
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

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMatrixPhysical
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
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N k : ℕ}

variable (S : PrescribedTree (L+1)) (a : S.Leaf) (K : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
include hb hm hmono hpos hroot hend hB hf

omit T q in
lemma integrable_rootShapeHistory_general
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0)
    (hk : 0 < k) (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool) :
    Integrable (fun z : FullRootState Y X (Labels L (Site N)) M × Site N =>
      rootShapeHistory S a K m base old read F spinAnchor f z.1 z.2)
      ((fullRootLaw ξ μ ν rate score).prod (siteLaw N)) := by
  have he : (fun z : FullRootState Y X (Labels L (Site N)) M × Site N =>
      rootShapeHistory S a K m base old read F spinAnchor f z.1 z.2) =
      (fun z => ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        rootHistory S a K m base old read
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f z.1 z.2) := by
    funext z
    exact rootShapeHistory_expansion S a K m base old read F spinAnchor f z.1 z.2
  rw [he]
  apply integrable_finsetSum
  intro s hs
  exact (integrable_rootHistory ξ μ ν (siteLaw N) rate score S a K m base old read
    (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
    (fun j => (requirementMap s j).2.2) spinAnchor f hb hm hmono hpos hroot hend hB hf hk).const_mul _

end DilutedSpinGlass.UniversalDictionary
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
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableProjector
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

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProjectionIntegrability
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
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N L : ℕ}
omit [Fintype Ω] in
lemma treeOverlap_eq_spatialProduct (S : PrescribedTree L) (f : FinitePath Ω L → Fin N → ℝ)
    (x : Sample Ω S) : treeOverlap S f x=spatialProduct (fun _ : S.Leaf => f) (fun b => S.pathAt b x) := by
  simp only [treeOverlap,spatialProduct,leafProduct_eq_prod]
end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableShapeEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma covarianceEnergy_le_four (P : FiniteLaw Ω) (X : Ω → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) : P.covarianceEnergy X≤4 := by
  by_cases hN : N=0
  · simp [covarianceEnergy,hN]
  · have hpos : 0<(N:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
    unfold covarianceEnergy
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, (4:ℝ) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        have h1 : |P.expect (fun x => X x i*X x j)|≤1 := P.abs_expect_le (fun x => by
          rw [abs_mul]; exact (mul_le_mul (hX x i) (hX x j) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
        have h2 : |P.expect (fun x => X x i)*P.expect (fun x => X x j)|≤1 := by
          rw [abs_mul]
          exact (mul_le_mul (P.abs_expect_le (fun x => hX x i)) (P.abs_expect_le (fun x => hX x j))
            (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
        have h : |P.covariance (fun x => X x i) (fun x => X x j)|≤2 := by
          exact (abs_sub _ _).trans (by linarith)
        have hs := sq_le_sq.mpr (show |P.covariance (fun x => X x i) (fun x => X x j)|≤|(2:ℝ)| by simpa using h)
        norm_num at hs
        exact hs
      _ = _ := by simp; ring

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n N : ℕ}

lemma measurable_child_expect_tilt (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (m : Fin (n+1) → ℝ) {f : Z → FinitePath Ω (n+1) → ℝ}
    {g : Z → Ω × C.Sample Ω → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ a, Measurable (fun z => g z a)) :
    Measurable (fun z => ((KernelTower.tilt (n+1) T m (f z)).1.bind
      (fun a => C.sampleLaw ((KernelTower.tilt (n+1) T m (f z)).2 a))).expect (g z)) := by
  simp_rw [FiniteLaw.expect_bind]
  apply T.1.measurable_tilt_expect (m 0)
  · intro a
    exact KernelTower.measurable_backwardLog n (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
  · intro a
    exact measurable_tilt_sample_expect C (T.2 a) (fun j => m j.succ)
      (fun y => hf (a,y)) (fun y => hg (a,y))

lemma measurable_childEnergy_tilt (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (m : Fin (n+1) → ℝ) {f : Z → FinitePath Ω (n+1) → ℝ}
    {X : Z → FinitePath Ω (n+1) → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => childEnergy C (KernelTower.tilt (n+1) T m (f z)) (X z)) := by
  have hY (a : Ω × C.Sample Ω) (i : Fin N) :
      Measurable (fun z => C.leafProduct (fun y => X z (a.1,y) i) a.2) :=
    measurable_leafProduct C (fun y => hX (a.1,y) i) a.2
  unfold childEnergy FiniteLaw.covarianceEnergy FiniteLaw.covariance
  apply Measurable.div_const
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  exact (measurable_child_expect_tilt C T m hf (fun a => (hY a i).mul (hY a j))).sub
    ((measurable_child_expect_tilt C T m hf (fun a => hY a i)).mul
      (measurable_child_expect_tilt C T m hf (fun a => hY a j)))

lemma measurable_shapeEnergyAt_tilt (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (m : Fin (n+1+d) → ℝ)
    {f : Z → FinitePath Ω (n+1+d) → ℝ} {X : Z → FinitePath Ω (n+1+d) → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => shapeEnergyAt C d (KernelTower.tilt (n+1+d) T m (f z)) (X z)) := by
  induction d with
  | zero => exact measurable_childEnergy_tilt C T m hf hX
  | succ d ih =>
    apply T.1.measurable_tilt_expect (m 0)
    · intro a
      exact KernelTower.measurable_backwardLog (n+1+d) (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
    · intro a
      exact ih (T.2 a) (fun j => m j.succ) (fun y => hf (a,y)) (fun y i => hX (a,y) i)

lemma shapeEnergyAt_le_four (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (X : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : shapeEnergyAt C d T X≤4 := by
  induction d with
  | zero =>
      unfold shapeEnergyAt childEnergy
      apply FiniteLaw.covarianceEnergy_le_four
      intro a i
      exact leafProduct_bound C (fun y => hX (a.1,y) i) a.2
  | succ d ih =>
      exact (T.1.expect_mono (fun a => ih (T.2 a) (fun y => X (a,y))
        (fun y i => hX (a,y) i))).trans_eq (T.1.expect_const 4)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootShapeEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n : ℕ}

section Shape
variable (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (Q : (i : I) → Fin (n+1+d) → FiniteLaw (A i))
    (m : Fin (n+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+1+d) → ℝ)
    (old : (i : I) → FinitePath Ω (n+1+d) → FinitePath (A i) (n+1+d) → ℝ)
    (V : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootShapeEnergy : Measurable (fun z : FullRootState Y X I M =>
    shapeEnergyAt C d (rootTower T Q m base old z) (rootVector V z)) := by
  change Measurable (packRoot (fun h k x n y =>
    shapeEnergyAt C d (KernelTower.tilt _ (tower (rootArray n y) _ T Q) m
      (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) _ w))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_shapeEnergyAt_tilt C d (tower (rootArray n y) _ T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ _ => measurable_const

include hb in
lemma integrable_rootShapeEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
      shapeEnergyAt C d (rootTower T Q m base old z) (rootVector V z)) μ := by
  apply Integrable.of_bound (measurable_rootShapeEnergy C d T Q m base old V hb).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (shapeEnergyAt_nonneg C d _ _)]
  exact shapeEnergyAt_le_four C d _ _ (fun y i => hV _ i)
end Shape

end DilutedSpinGlass.HeterogeneousMarks
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

end DilutedSpinGlass.DepthAverage
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

lemma scheduledShapeEnergy_eq_realize (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : L=n+1+d) (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) :
    scheduledShapeEnergy L d S q T f =
      shapeEnergyAt (realize n (d+1) S q) d (kernelHeightCast h T) (vectorHeightCast h f) := by
  subst L
  unfold scheduledShapeEnergy
  rw [dite_eq_left (by omega : d<n+1+d)]
  have he (n' : ℕ) (hn : n'=n) (hc : n+1+d=n'+1+d) :
      shapeEnergyAt (realize n' (d+1) S q) d (kernelHeightCast hc T) (vectorHeightCast hc f) =
        shapeEnergyAt (realize n (d+1) S q) d T f := by
    subst n'
    rfl
  exact he _ (by omega) _

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootChildMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

/-- Probability-root Jensen for the square root, proved directly from the
nonnegative centered square. It is used twice in the multileaf induction. -/
lemma integral_sqrt_le_sqrt_integral {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (f : Z → ℝ)
    (hf : Integrable f μ) (hs : Integrable (fun z => Real.sqrt (f z)) μ)
    (h : ∀ z, 0≤f z) : (∫ z, Real.sqrt (f z) ∂μ)≤Real.sqrt (∫ z, f z ∂μ) := by
  let t := ∫ z, Real.sqrt (f z) ∂μ
  have ht : 0≤t := integral_nonneg (fun _ => Real.sqrt_nonneg _)
  have he (z : Z) : (Real.sqrt (f z)-t)^2=f z-(2*t)*Real.sqrt (f z)+t^2 := by
    have hs := Real.sq_sqrt (h z)
    nlinarith
  have hp : 0≤∫ z, (Real.sqrt (f z)-t)^2 ∂μ := integral_nonneg (fun z => sq_nonneg _)
  simp_rw [he] at hp
  have hm : Integrable (fun z => (2*t)*Real.sqrt (f z)) μ := hs.const_mul (2*t)
  have hd : Integrable (fun z => f z-(2*t)*Real.sqrt (f z)) μ := hf.sub hm
  rw [integral_add hd (integrable_const (t^2)),
    integral_sub hf hm,integral_const_mul,integral_const] at hp
  simp only [probReal_univ,one_smul] at hp
  have hsq : t^2 ≤ ∫ z, f z ∂μ := by dsimp only [t] at *; nlinarith
  exact (Real.sqrt_sq ht).symm.le.trans (Real.sqrt_le_sqrt hsq)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AveragedMatrixSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open Filter
open scoped Topology BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

/-- At each fixed grid, there are only finitely many depth assignments. Thus
the signed physical identity error can be averaged BEFORE the size limit. -/
theorem tendsto_average_zero (D : (α → Fin L) → Prop)
    (F : ℕ → (α → Fin L) → ℝ)
    (hF : ∀ q, Tendsto (fun n => F n q) atTop (𝓝 0)) :
    Tendsto (fun n => average D (F n)) atTop (𝓝 0) := by
  classical
  simp only [average_eq]
  have hs := tendsto_finsetSum (Finset.univ.filter D) (fun q _ => hF q)
  have hh := hs.div_const ((L:ℝ)^Fintype.card α)
  simpa only [Finset.sum_const_zero,zero_div] using hh

end DilutedSpinGlass.DepthAverage
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

end DilutedSpinGlass.UniversalDictionary
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

noncomputable local instance scheduledEnergyBoundDecidableEq_r802ef5_1 (type : Type) :
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
lemma physicalShapeAverage_le_one (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    physicalShapeAverage M θB hB N L u S η≤1 :=
  DepthAverage.average_le_const _ _ zero_le_one
    (fun Q _ => physicalScheduledEnergy_le_one M θB hB N L u S Q)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRegularSelection
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

noncomputable local instance fullRegularSelectionDecidableEq_r802ef5_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance markerHistoryDecidable_r802ef5_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype Ω] in
/-- If every requested new color has a different split from a protected
marker than every available old leaf, the old choices vanish in the literal
signed history. Fresh extensions retain this exclusion. -/
theorem weightedMatrixHistory_drop_available (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (m : Fin (n+1) → ℝ) (a : C) (cs : List C) (hcs : cs.Nodup) (ha : a ∉ cs)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hsep : ∀ c ∈ cs, ∀ i ∈ U,
      splitDepth S (loc i) (pos a) ≠ splitDepth T (q c) (q a))
    (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q V m cs S U loc pos f =
      weightedMatrixHistory T q V m cs S ∅ loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    have hnd := List.nodup_cons.mp hcs
    have hac : a ≠ c := fun h => ha (by simp [h])
    have ha' : a ∉ cs := fun h => ha (by simp [h])
    change (∑ i ∈ U, weightedMatrixHistory T q V m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) +
      ∑ v : S.Internal, gamma S m v * weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = _
    have ho : (∑ i ∈ U, weightedMatrixHistory T q V m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) = 0 := by
      apply Finset.sum_eq_zero
      intro index hindex
      apply weightedMatrixHistory_mismatch T q V m cs S (U.erase index) loc _ f c a hnd.1 ha'
      simpa only [Function.update_self,Function.update_of_ne hac] using
        hsep c (by simp) index hindex
    rw [ho,zero_add]
    change _ = (∑ i ∈ (∅ : Finset ι), _) + _
    simp only [Finset.sum_empty,zero_add]
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    apply ih hnd.2 ha'
    intro d hd i hi
    simpa only [Function.update_of_ne hac,splitDepth_old_old] using hsep d (by simp [hd]) i hi

/-- General complete-matrix normalization with a whole protected old tree.
All paths, including those used by an old observable, are jointly retained. -/
theorem weightedMatrixHistory_protected_one (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Bijective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C) (hP : P.Nonempty)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset=Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b)=splitDepth T (q a) (q b))
    (A : (C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)))
      m cs S U loc pos (fun _ => 1) =
      (partialKappa T m (Finset.univ.image q)/partialKappa T m (P.image q)) *
        (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z)) := by
  let B := (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z))
  have he := labeledHistory_congr_one m
    (fun D pos g => if ∀ a b, splitDepth D (pos a) (pos b)=splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)) else 0)
    (fun D pos g => B*(if ∀ a b, splitDepth D (pos a) (pos b)=splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect g else 0))
    (by
      intro D pos
      split_ifs with h
      · simp only [one_mul,FiniteLaw.expect_const,mul_one]
        exact matrix_paths_expect T D q hq.2 pos h K A
      · exact (mul_zero B).symm)
    cs S U loc pos
  unfold weightedMatrixHistory
  rw [he,labeledHistory_mul_left]
  change B * matrixHistory T q K m cs S U loc pos (fun _ => 1) = _
  rw [matrixHistory_normalization T q hq.1 K m hm hp hend cs hcs P hP hdis hfull
    S U loc pos hcover hsplit (fun _ => 1)]
  simp only [FiniteLaw.expect_const,mul_one]
  exact mul_comm _ _

omit [Fintype Ω] [Fintype C] in
/-- Split relations among colors which are never reassigned survive all
old and fresh extensions. This transports an exact terminal identity through
the actual signed expansion. -/
theorem labeledHistory_congr_protected_split (m : Fin (n+1) → ℝ)
    (V W : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (P : Finset C) (B : C → C → ℕ)
    (h : ∀ R pos, (∀ a ∈ P, ∀ b ∈ P, splitDepth R (pos a) (pos b)=B a b) →
      ∀ g, V R pos g=W R pos g)
    (cs : List C) (hdis : ∀ c ∈ cs, c ∉ P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P, splitDepth S (pos a) (pos b)=B a b)
    (f : Sample Ω S → ℝ) :
    labeledHistory m V cs S U loc pos f=labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => exact h S pos hsplit f
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hdis' : ∀ d ∈ cs, d ∉ P := fun d hd => hdis d (by simp [hd])
    simp only [labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      apply ih hdis'
      intro a ha b hb
      simpa only [Function.update_of_ne (fun e : a=c => hc (e ▸ ha)),
        Function.update_of_ne (fun e : b=c => hc (e ▸ hb))] using hsplit a ha b hb
    · apply Finset.sum_congr rfl
      intro v _
      congr 1
      apply ih hdis'
      intro a ha b hb
      simpa only [Function.update_of_ne (fun e : a=c => hc (e ▸ ha)),
        Function.update_of_ne (fun e : b=c => hc (e ▸ hb)),splitDepth_old_old] using hsplit a ha b hb

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerHistoryTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C D ι : Type} [Fintype Ω] [DecidableEq C] [DecidableEq D] [DecidableEq ι] {n : ℕ}

noncomputable local instance markerHistoryTransportDecidable_r802ef5_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype Ω] in
/-- Enlarging the color set by protected old paths does not change any
extension choice or its coefficient. -/
theorem labeledHistory_reindex (m : Fin (n+1) → ℝ) (e : C → D) (he : Function.Injective e)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : D → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => V R (pos ∘ e) g) (cs.map e) S U loc pos f =
      labeledHistory m V cs S U loc (pos ∘ e) f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons,labeledHistory,ih,Function.update_comp_eq_of_injective _ he]
    rfl

/-- In a splitting ultrametric, a path separating from a marker before every
old path has the same split from each of those old paths. -/
lemma splitDepth_eq_of_lt (S : PrescribedTree n) (a b c : S.Leaf)
    (h : splitDepth S a b < splitDepth S b c) :
    splitDepth S a c = splitDepth S a b := by
  have h₁ := splitDepth_ultrametric S a b c
  have h₂ := splitDepth_ultrametric S a c b
  rw [splitDepth_symm S c b] at h₂
  omega

variable [Fintype C] [Fintype D]

omit [DecidableEq C] [DecidableEq D] [Fintype C] [Fintype D] in
/-- A matrix on the new colors and a single marker determines all their
splits from the protected old tree when the old tree has not yet branched at
the prescribed separation depth. -/
theorem marker_matrix_iff (S Q : PrescribedTree n)
    (old : D → S.Leaf) (fresh : C → S.Leaf) (a : D)
    (qold : D → Q.Leaf) (qfresh : C → Q.Leaf)
    (hold : ∀ d e, splitDepth S (old d) (old e)=splitDepth Q (qold d) (qold e))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a) < splitDepth Q (qold a) (qold d)) :
    (∀ x y : Option C,
      splitDepth S (Option.elim' (old a) fresh x) (Option.elim' (old a) fresh y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y)) ↔
    (∀ x y : D ⊕ C,
      splitDepth S (Sum.elim old fresh x) (Sum.elim old fresh y)=
      splitDepth Q (Sum.elim qold qfresh x) (Sum.elim qold qfresh y)) := by
  constructor
  · intro h x y
    have hcross (c : C) (d : D) : splitDepth S (fresh c) (old d)=splitDepth Q (qfresh c) (qold d) := by
      have hm := h (some c) none
      change splitDepth S (fresh c) (old a)=splitDepth Q (qfresh c) (qold a) at hm
      have hs : splitDepth S (fresh c) (old a) < splitDepth S (old a) (old d) := by
        rw [hm,hold]; exact hsep c d
      rw [splitDepth_eq_of_lt S _ _ _ hs,hm,splitDepth_eq_of_lt Q _ _ _ (hsep c d)]
    cases x with
    | inl d =>
      cases y with
      | inl e => exact hold d e
      | inr c => simpa only [Sum.elim_inl,Sum.elim_inr,splitDepth_symm] using hcross c d
    | inr c =>
      cases y with
      | inl d => exact hcross c d
      | inr b => exact h (some c) (some b)
  · intro h x y
    have hh := h (Option.elim' (Sum.inl a) Sum.inr x) (Option.elim' (Sum.inl a) Sum.inr y)
    cases x <;> cases y <;> exact hh

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerJointHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] {n : ℕ}

omit [Fintype C] in
lemma markerEmbedding_injective {D : Type} (a : D) : Function.Injective (markerEmbedding (C := C) a) := by
  intro x y h
  cases x <;> cases y <;> simp_all [markerEmbedding]

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.markerJointHistoryDecidableEq
noncomputable local instance markerJointHistoryDecidable_r802ef5_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- Exact enlargement of the signed marker history by all the protected old
paths. The matrix constraints force the added tree to separate before the
old tree branches; no old-position branch is silently retained or discarded. -/
theorem marker_history_augment
    (S T Q : PrescribedTree n) (a : S.Leaf) (q : Option C → T.Leaf)
    (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hold : ∀ d e, splitDepth S d e=splitDepth Q (qold d) (qold e))
    (hmarker : ∀ x y : Option C,
      splitDepth T (q x) (q y)=
        splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a) < splitDepth Q (qold a) (qold d))
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (cs : List C) (hcs : cs.Nodup)
    (F : (S.Leaf → FinitePath Ω n) → ℝ) (A : (Option C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)))
      m (cs.map some) S (Finset.univ.erase a) id (fun _ => a)
      (fun z => F (fun d => S.pathAt d z)) =
    weightedMatrixHistory Q (Sum.elim qold qfresh)
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z *
        (F (fun d => R.pathAt (pos (Sum.inl d)) z) *
          A (fun c => R.pathAt (pos (markerEmbedding a c)) z))))
      m (cs.map Sum.inr) S (∅ : Finset S.Leaf) id (Sum.elim id (fun _ => a)) (fun _ => 1) := by
  let e := markerEmbedding (C := C) a
  let P : Finset (S.Leaf ⊕ C) := Finset.univ.image Sum.inl
  let V := fun (R : PrescribedTree n) (pos : Option C → R.Leaf) (g : Sample Ω R → ℝ) =>
    if ∀ x y, splitDepth R (pos x) (pos y)=splitDepth T (q x) (q y)
    then (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)) else 0
  have hdis : ∀ c ∈ cs.map Sum.inr, c ∉ P := by
    intro c hc hp
    rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
    simp [P] at hp
  have hsplit : ∀ x ∈ P, ∀ y ∈ P,
      splitDepth S (Sum.elim id (fun _ : C => a) x) (Sum.elim id (fun _ : C => a) y)=
        splitDepth Q (Sum.elim qold qfresh x) (Sum.elim qold qfresh y) := by
    rintro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨d,hd,rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b,hb,rfl⟩
    exact hold d b
  rw [weightedMatrixHistory_drop_available T q _ m none _ (hcs.map (Option.some_injective C))
    (by simp) S (Finset.univ.erase a) id (fun _ => a) (by
      intro c hc d hd
      rcases List.mem_map.mp hc with ⟨c,hc,rfl⟩
      have hs := hsep c d
      simp only [id_eq,hold,hmarker,Option.elim']
      rw [splitDepth_symm Q (qold d) (qold a)]
      exact (ne_of_lt hs).symm) _]
  change labeledHistory m V (cs.map some) S ∅ id (fun _ => a) _ = _
  have hre := labeledHistory_reindex m e (markerEmbedding_injective a) V (cs.map some)
    S (∅ : Finset S.Leaf) id (Sum.elim id (fun _ => a)) (fun z => F (fun d => S.pathAt d z))
  have hmap : (cs.map some).map e=cs.map Sum.inr := by simp [List.map_map,e,markerEmbedding,Function.comp_def]
  have hpos : Sum.elim id (fun _ : C => a) ∘ e = fun _ => a := by
    funext c; cases c <;> rfl
  rw [hmap,hpos] at hre
  rw [← hre]
  let G := fun x : (S.Leaf ⊕ C → FinitePath Ω n) => F (fun d => x (Sum.inl d))
  have hpull := labeledHistory_protected_function m (fun R pos g => V R (pos ∘ e) g)
    P G (by
      intro x y h
      apply congrArg F
      funext d
      exact h (Sum.inl d) (by simp [P])) (cs.map Sum.inr) hdis
    S (∅ : Finset S.Leaf) id (Sum.elim id (fun _ => a)) (fun _ => 1)
  simp only [one_mul,G,Sum.elim_inl,id_eq] at hpull
  rw [← hpull]
  unfold weightedMatrixHistory
  apply labeledHistory_congr_protected_split m _ _ P
    (fun x y => splitDepth Q (Sum.elim qold qfresh x) (Sum.elim qold qfresh y)) _
    (cs.map Sum.inr) hdis S ∅ id _ hsplit
  intro R pos hR g
  have hr : ∀ d b, splitDepth R (pos (Sum.inl d)) (pos (Sum.inl b))=
      splitDepth Q (qold d) (qold b) := fun d b => hR _ (by simp [P]) _ (by simp [P])
  have hm := marker_matrix_iff R Q (fun d => pos (Sum.inl d)) (fun c => pos (Sum.inr c)) a qold qfresh hr hsep
  have hopt : pos ∘ e = Option.elim' (pos (Sum.inl a)) (fun c => pos (Sum.inr c)) := by
    funext c; cases c <;> rfl
  have hsum : Sum.elim (fun d => pos (Sum.inl d)) (fun c => pos (Sum.inr c)) = pos := by
    funext c; cases c <;> rfl
  have htest : (∀ x y, splitDepth R ((pos ∘ e) x) ((pos ∘ e) y)=splitDepth T (q x) (q y)) ↔
      (∀ x y, splitDepth R (pos x) (pos y)=splitDepth Q (Sum.elim qold qfresh x) (Sum.elim qold qfresh y)) := by
    simpa only [hmarker,hopt,hsum] using hm
  dsimp only [V]
  simp only [htest]
  split_ifs
  · apply FiniteLaw.expect_congr
    intro z
    simp only [Function.comp_def,e,mul_assoc]
  · rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

lemma markerLeaf_bijective (A : PrescribedTree n) : Function.Bijective (markerLeaf A) := by
  constructor
  · intro x y h
    cases x with
    | none => cases y with
      | none => rfl
      | some b => have hh := congrArg Sigma.fst h; norm_num [markerLeaf] at hh
    | some a => cases y with
      | none => have hh := congrArg Sigma.fst h; norm_num [markerLeaf] at hh
      | some b => exact congrArg some ((Sigma.mk.inj h).2.eq)
  · rintro ⟨i,b⟩
    fin_cases i
    · have hb := leaf_single_unique n b
      subst b
      exact ⟨none,rfl⟩
    · exact ⟨some b,rfl⟩

lemma doubledLeaf_bijective (A : PrescribedTree n) : Function.Bijective (doubledLeaf A) := by
  constructor
  · intro x y h
    cases x with
    | inl a => cases y with
      | inl b => exact congrArg Sum.inl ((Sigma.mk.inj h).2.eq)
      | inr b => have hh := congrArg Sigma.fst h; norm_num [markerLeaf,doubledLeaf] at hh
    | inr a => cases y with
      | inl b => have hh := congrArg Sigma.fst h; norm_num [markerLeaf,doubledLeaf] at hh
      | inr b => exact congrArg Sum.inr ((Sigma.mk.inj h).2.eq)
  · rintro ⟨i,b⟩
    fin_cases i
    · exact ⟨Sum.inl b,rfl⟩
    · exact ⟨Sum.inr b,rfl⟩

lemma markerTarget_bijective (A : PrescribedTree n) (r : ℕ) :
    Function.Bijective (markerTarget A r) :=
  (stemLeaf_bijective _ r).comp (markerLeaf_bijective A)

lemma markerJoint_bijective (A : PrescribedTree n) (r : ℕ) :
    Function.Bijective (Sum.elim (markerOld A r) (markerFresh A r)) := by
  have h := (stemLeaf_bijective (doubled A) r).comp ((doubledLeaf_bijective A).comp
    (Equiv.sumCongr (markerOldIndex A r) (Equiv.refl A.Leaf)).bijective)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases x <;> rfl

lemma split_unary (A : PrescribedTree n) (a b : A.Leaf) :
    splitDepth (unary A) (unaryLeafEquiv A a) (unaryLeafEquiv A b)=1+splitDepth A a b :=
  @splitDepth_same_child n (1:ℕ+) (fun _ : Fin 1 => A) 0 a b

lemma split_doubled_same (A : PrescribedTree n) (a b : A.Leaf) (i : Fin 2) :
    splitDepth (doubled A) ⟨i,a⟩ ⟨i,b⟩=1+splitDepth A a b :=
  @splitDepth_same_child n (2:ℕ+) (fun _ : Fin 2 => A) i a b

lemma split_doubled_diff (A : PrescribedTree n) (a b : A.Leaf) (i j : Fin 2) (h : i ≠ j) :
    splitDepth (doubled A) ⟨i,a⟩ ⟨j,b⟩=0 :=
  @splitDepth_diff_child n (2:ℕ+) (fun _ : Fin 2 => A) i j h a b

lemma split_marker_none_some (A : PrescribedTree n) (b : A.Leaf) :
    splitDepth (markerFork A) (markerLeaf A none) (markerLeaf A (some b))=0 :=
  @splitDepth_diff_child n (2:ℕ+) (fun i : Fin 2 => Fin.cases (motive := fun _ => PrescribedTree n) (single n) (fun _ : Fin 1 => A) i) 0 1 (by decide) _ _

lemma split_marker_some_none (A : PrescribedTree n) (b : A.Leaf) :
    splitDepth (markerFork A) (markerLeaf A (some b)) (markerLeaf A none)=0 :=
  @splitDepth_diff_child n (2:ℕ+) (fun i : Fin 2 => Fin.cases (motive := fun _ => PrescribedTree n) (single n) (fun _ : Fin 1 => A) i) 1 0 (by decide) _ _

lemma split_marker_some_some (A : PrescribedTree n) (b c : A.Leaf) :
    splitDepth (markerFork A) (markerLeaf A (some b)) (markerLeaf A (some c))=1+splitDepth A b c :=
  @splitDepth_same_child n (2:ℕ+) (fun i : Fin 2 => Fin.cases (motive := fun _ => PrescribedTree n) (single n) (fun _ : Fin 1 => A) i) 1 b c

lemma markerOldIndex_stem (A : PrescribedTree n) (r : ℕ) (c : A.Leaf) :
    markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A c))=c := by
  exact congrArg (unaryLeafEquiv A).symm
    ((stemLeafEquiv (unary A) r).symm_apply_apply (unaryLeafEquiv A c))

lemma markerOld_split (A : PrescribedTree n) (r : ℕ) (a b : (stem (unary A) r).Leaf) :
    splitDepth (stem (unary A) r) a b=
      splitDepth (stem (doubled A) r) (markerOld A r a) (markerOld A r b) := by
  obtain ⟨a,rfl⟩ := ((unaryLeafEquiv A).trans (stemLeafEquiv (unary A) r)).surjective a
  obtain ⟨b,rfl⟩ := ((unaryLeafEquiv A).trans (stemLeafEquiv (unary A) r)).surjective b
  have hS := splitDepth_stem (unary A) r (unaryLeafEquiv A a) (unaryLeafEquiv A b)
  have hQ := splitDepth_stem (doubled A) r
    ⟨0,markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A a))⟩
    ⟨0,markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A b))⟩
  have heq : splitDepth (unary A) (unaryLeafEquiv A a) (unaryLeafEquiv A b)=
      splitDepth (doubled A)
        ⟨0,markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A a))⟩
        ⟨0,markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A b))⟩ := by
    exact (split_unary A a b).trans ((congrArg (fun x => 1+x)
      (congrArg₂ (splitDepth A) (markerOldIndex_stem A r a).symm
        (markerOldIndex_stem A r b).symm)).trans
        (split_doubled_same A _ _ 0).symm)
  exact hS.trans ((congrArg (fun x => x+r) heq).trans hQ.symm)

lemma markerTarget_split (A : PrescribedTree n) (r : ℕ) (a : (stem (unary A) r).Leaf)
    (x y : Option A.Leaf) :
    splitDepth (stem (markerFork A) r) (markerTarget A r x) (markerTarget A r y)=
      splitDepth (stem (doubled A) r)
        (Option.elim' (markerOld A r a) (markerFresh A r) x)
        (Option.elim' (markerOld A r a) (markerFresh A r) y) := by
  have hT := splitDepth_stem (markerFork A) r (markerLeaf A x) (markerLeaf A y)
  cases x with
  | none => cases y with
    | none => simp only [Option.elim',splitDepth_self]
    | some b =>
      have hQ := splitDepth_stem (doubled A) r ⟨0,markerOldIndex A r a⟩ ⟨1,b⟩
      have ht := split_marker_none_some A b
      have hq := split_doubled_diff A (markerOldIndex A r a) b 0 1 (by decide)
      exact hT.trans ((congrArg (fun x => x+r) (ht.trans hq.symm)).trans hQ.symm)
  | some b => cases y with
    | none =>
      have hQ := splitDepth_stem (doubled A) r ⟨1,b⟩ ⟨0,markerOldIndex A r a⟩
      have ht := split_marker_some_none A b
      have hq := split_doubled_diff A b (markerOldIndex A r a) 1 0 (by decide)
      exact hT.trans ((congrArg (fun x => x+r) (ht.trans hq.symm)).trans hQ.symm)
    | some c =>
      have hQ := splitDepth_stem (doubled A) r ⟨1,b⟩ ⟨1,c⟩
      have ht := split_marker_some_some A b c
      have hq := split_doubled_same A b c 1
      exact hT.trans ((congrArg (fun x => x+r) (ht.trans hq.symm)).trans hQ.symm)

lemma marker_split_separation (A : PrescribedTree n) (r : ℕ)
    (a d : (stem (unary A) r).Leaf) (c : A.Leaf) :
    splitDepth (stem (doubled A) r) (markerFresh A r c) (markerOld A r a) <
      splitDepth (stem (doubled A) r) (markerOld A r a) (markerOld A r d) := by
  have hL := splitDepth_stem (doubled A) r ⟨1,c⟩ ⟨0,markerOldIndex A r a⟩
  have hR := splitDepth_stem (doubled A) r ⟨0,markerOldIndex A r a⟩ ⟨0,markerOldIndex A r d⟩
  have hl := split_doubled_diff A c (markerOldIndex A r a) 1 0 (by decide)
  have hr := split_doubled_same A (markerOldIndex A r a) (markerOldIndex A r d) 0
  have hL' := hL.trans (congrArg (fun x => x+r) hl)
  have hR' := hR.trans (congrArg (fun x => x+r) hr)
  have hh : 0+r < (1+splitDepth A (markerOldIndex A r a) (markerOldIndex A r d))+r := by omega
  exact lt_of_eq_of_lt hL' (lt_of_lt_of_eq hh hR'.symm)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerNormalization
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] {n : ℕ}

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.markerNormalizationPropDecidable
omit [Fintype C] in
lemma all_old_history_cover (S : PrescribedTree n) (a : S.Leaf) :
    HistoryCover S (∅ : Finset S.Leaf) id
      (Finset.univ.image (Sum.inl : S.Leaf → S.Leaf ⊕ C)) (Sum.elim id (fun _ => a)) := by
  classical
  refine ⟨⟨Function.injective_id, ?_, by simp⟩, ?_⟩
  · intro x hx y hy h
    rcases Finset.mem_image.mp hx with ⟨d,hd,rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b,hb,rfl⟩
    exact congrArg Sum.inl h
  · intro b
    exact Or.inr ⟨Sum.inl b, by simp, rfl⟩

lemma marker_history_joint_ratio (S T Q : PrescribedTree n) (a : S.Leaf)
    (q : Option C → T.Leaf) (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hqQ : Function.Bijective (Sum.elim qold qfresh))
    (hold : ∀ d e, splitDepth S d e=splitDepth Q (qold d) (qold e))
    (hmarker : ∀ x y, splitDepth T (q x) (q y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a) < splitDepth Q (qold a) (qold d))
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (hfull : cs.toFinset=Finset.univ)
    (F : (S.Leaf → FinitePath Ω n) → ℝ) (A : (Option C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)))
      m (cs.map some) S (Finset.univ.erase a) id (fun _ => a)
      (fun z => F (fun d => S.pathAt d z)) =
    (partialKappa Q m (Finset.univ.image (Sum.elim qold qfresh)) /
      partialKappa Q m ((Finset.univ.image Sum.inl).image (Sum.elim qold qfresh))) *
      (Q.sampleLaw K).expect (fun z => F (fun d => Q.pathAt (qold d) z) *
        A (fun c => Q.pathAt (Option.elim' (qold a) qfresh c) z)) := by
  classical
  have hmem (c : C) : c ∈ cs := by
    have : c ∈ cs.toFinset := by rw [hfull]; simp
    simpa using this
  rw [marker_history_augment S T Q a q qold qfresh hold hmarker hsep K m cs hcs F A]
  have h := weightedMatrixHistory_protected_one Q (Sum.elim qold qfresh) hqQ K m hm hp hend
    (cs.map Sum.inr) (hcs.map Sum.inr_injective) (Finset.univ.image Sum.inl)
    (by exact ⟨Sum.inl a, by simp⟩) (by
      intro c hc
      rcases List.mem_map.mp hc with ⟨c,hc,rfl⟩
      simp) (by
      ext x
      cases x with
      | inl d => simp
      | inr c => simp [hmem])
    S (∅ : Finset S.Leaf) id (Sum.elim id (fun _ => a)) (all_old_history_cover S a)
    (by
      rintro x hx y hy
      rcases Finset.mem_image.mp hx with ⟨d,hd,rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b,hb,rfl⟩
      exact hold d b)
    (fun x => F (fun d => x (Sum.inl d))*A (x ∘ markerEmbedding a))
  convert h using 1
  · rfl
  · congr 2
    funext z
    congr 1
    apply congrArg A
    funext c
    cases c <;> rfl

/-- The exact marker history coefficient is the anchor-alone kappa; this
proof obtains the equality by normalization of the *same* histories, without
an independent combinatorial simplification of kappa. -/
theorem marker_history_joint (S T Q : PrescribedTree n) (a : S.Leaf)
    (q : Option C → T.Leaf) (hq : Function.Bijective q)
    (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hqQ : Function.Bijective (Sum.elim qold qfresh))
    (hold : ∀ d e, splitDepth S d e=splitDepth Q (qold d) (qold e))
    (hmarker : ∀ x y, splitDepth T (q x) (q y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a) < splitDepth Q (qold a) (qold d))
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (hfull : cs.toFinset=Finset.univ)
    (F : (S.Leaf → FinitePath Ω n) → ℝ) (A : (Option C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)))
      m (cs.map some) S (Finset.univ.erase a) id (fun _ => a)
      (fun z => F (fun d => S.pathAt d z)) =
    partialKappa T m (Finset.univ.image q) *
      (Q.sampleLaw K).expect (fun z => F (fun d => Q.pathAt (qold d) z) *
        A (fun c => Q.pathAt (Option.elim' (qold a) qfresh c) z)) := by
  classical
  have hmem (c : C) : c ∈ cs := by
    have : c ∈ cs.toFinset := by rw [hfull]; simp
    simpa using this
  have hn := weightedMatrixHistory_one T q hq K m hm hp hend none
    (cs.map some) (hcs.map (Option.some_injective C)) (by simp)
    (by ext x; cases x <;> simp [hmem]) S a (fun _ => 1)
  have hr := marker_history_joint_ratio S T Q a q qold qfresh hqQ hold hmarker hsep
    K m hm hp hend cs hcs hfull (fun _ => 1) (fun _ => 1)
  simp only [FiniteLaw.expect_const,mul_one] at hn hr
  rw [marker_history_joint_ratio S T Q a q qold qfresh hqQ hold hmarker hsep
    K m hm hp hend cs hcs hfull F A, ← hr, hn]

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerRootIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z C : Type} [MeasurableSpace Z] [Fintype C] {n : ℕ}

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.markerRootIdentityDecidable
/-- A marker identity controls the covariance of two whole overlaps, not
just a selected coordinate or a conditional covariance. All constants and
both actual finite-tree marginals are explicitly retained. -/
theorem marker_root_covariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S T Q : PrescribedTree n) (a : S.Leaf) (e : C ≃ S.Leaf)
    (q : Option C → T.Leaf) (hq : Function.Bijective q)
    (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hqQ : Function.Bijective (Sum.elim qold qfresh))
    (hold : ∀ d b, splitDepth S d b=splitDepth Q (qold d) (qold b))
    (hfresh : ∀ c d, splitDepth S (e c) (e d)=splitDepth Q (qfresh c) (qfresh d))
    (hmarker : ∀ x y, splitDepth T (q x) (q y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a) < splitDepth Q (qold a) (qold d))
    (K : (z : Z) → KernelTower (Ω z) n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (hfull : cs.toFinset=Finset.univ)
    (F : (z : Z) → (S.Leaf → FinitePath (Ω z) n) → ℝ) :
    matrixRootCovariance μ Ω T S q K m (cs.map some) a
      (fun z x => F z (fun d => x (some (e.symm d))))
      (fun z w => F z (fun d => S.pathAt d w)) =
    partialKappa T m (Finset.univ.image q) *
      ((∫ z, (Q.sampleLaw (K z)).expect (fun w =>
        F z (fun d => Q.pathAt (qold d) w) *
        F z (fun d => Q.pathAt (qfresh (e.symm d)) w)) ∂μ) -
      (∫ z, (S.sampleLaw (K z)).expect (fun w => F z (fun d => S.pathAt d w)) ∂μ)^2) := by
  classical
  have hmem (c : C) : c ∈ cs := by
    have : c ∈ cs.toFinset := by rw [hfull]; simp
    simpa using this
  have hmarg (z : Z) :
      (T.sampleLaw (K z)).expect (fun w => F z (fun d => T.pathAt (q (some (e.symm d))) w)) =
      (S.sampleLaw (K z)).expect (fun w => F z (fun d => S.pathAt d w)) := by
    have h := matrix_paths_expect S T id Function.surjective_id
      (fun d => q (some (e.symm d))) (by
        intro d b
        rw [hmarker]
        dsimp only [Option.elim',id_eq]
        rw [← hfresh,e.apply_symm_apply,e.apply_symm_apply]) (K z) (F z)
    exact h
  have holdHist (z : Z) := marker_history_joint S T Q a q hq qold qfresh hqQ hold
    hmarker hsep (K z) m hm hp hend cs hcs hfull (F z)
    (fun x => F z (fun d => x (some (e.symm d))))
  have honeHist (z : Z) := weightedMatrixHistory_one T q hq (K z) m hm hp hend none
    (cs.map some) (hcs.map (Option.some_injective C)) (by simp)
    (by ext x; cases x <;> simp [hmem]) S a
    (fun x => F z (fun d => x (some (e.symm d))))
  unfold matrixRootCovariance matrixObservableHistory
  simp_rw [holdHist,honeHist]
  simp only [Option.elim'_some]
  simp_rw [hmarg]
  rw [integral_const_mul,integral_const_mul]
  ring

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerPhysicalBridge
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N k : ℕ}

variable (S : PrescribedTree (L+1)) (a : S.Leaf) (K : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma integral_rootShapeHistory_marker (z : FullRootState Y X (Labels L (Site N)) M) :
    (∫ i, rootShapeHistory S a K m base old read (matrixSplitTest T q) false f z i ∂siteLaw N) =
      rootMarkerObservable S a K m base old read T q f z := by
  rw [integral_siteLaw]
  symm
  exact matrix_history_spatialProduct T q
    (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old z) m
    (fun c x i => match c with | none => 1 | some _ => rootVector (readVector read) z x i) S a
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
include hb hm hmono hpos hroot hend hB hf


lemma shapeAverage_marker (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) (hk : 0 < k) :
    shapeAverage ξ μ ν (siteLaw N) rate score S a K m base old read (matrixSplitTest T q) false f =
      ∫ z, rootMarkerObservable S a K m base old read T q f z ∂fullRootLaw ξ μ ν rate score := by
  unfold shapeAverage
  rw [integral_prod _ (integrable_rootShapeHistory_general S a K m base old read f
    hb hm hmono hpos hroot hend hB hf ξ μ ν rate score hk (matrixSplitTest T q) false)]
  exact integral_congr_ae (ae_of_all _ (fun z => integral_rootShapeHistory_marker S a K m base old read T q f z))

lemma shapeCovariance_marker (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) (hk : 0 < k) :
    shapeCovariance ξ μ ν (siteLaw N) rate score S a K m base old read (matrixSplitTest T q) false f =
      matrixRootCovariance (fullRootLaw ξ μ ν rate score)
        (rootAlphabet (Ω := Ω) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
        (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old) m
        (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse a
        (fun z => spatialProduct (fun c x i => match c with | none => 1 | some _ => rootVector (readVector read) z x i))
        (fun z x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x))) := by
  unfold shapeCovariance
  rw [shapeAverage_marker S a K m base old read T q f hb hm hmono hpos hroot hend hB hf
    ξ μ ν rate score hk,
    shapeAverage_marker S a K m base old read T q (fun _ => 1) hb hm hmono hpos hroot hend
    (by norm_num : (0:ℝ) ≤ 1) (fun _ => by simp) ξ μ ν rate score hk]
  rfl

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerConcrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable local instance instDecidable_12_r802ef5_1 (p : Prop) : Decidable p := Classical.propDecidable p
lemma markerFresh_split (A : PrescribedTree n) (r : ℕ) (c d : A.Leaf) :
    splitDepth (stem (unary A) r) ((markerOldIndex A r).symm c) ((markerOldIndex A r).symm d)=
      splitDepth (stem (doubled A) r) (markerFresh A r c) (markerFresh A r d) := by
  have hS := splitDepth_stem (unary A) r (unaryLeafEquiv A c) (unaryLeafEquiv A d)
  have hQ := splitDepth_stem (doubled A) r ⟨1,c⟩ ⟨1,d⟩
  exact hS.trans ((congrArg (fun x => x+r)
    ((split_unary A c d).trans (split_doubled_same A c d 1).symm)).trans hQ.symm)

lemma markerColorTarget_bijective (A : PrescribedTree n) (r : ℕ) :
    Function.Bijective (markerColorTarget A r) :=
  (markerTarget_bijective A r).comp (Equiv.optionCongr (markerColorEquiv A)).bijective

lemma markerColorJoint_bijective (A : PrescribedTree n) (r : ℕ) :
    Function.Bijective (Sum.elim (markerOld A r) (markerColorFresh A r)) := by
  have h := (markerJoint_bijective A r).comp
    (Equiv.sumCongr (Equiv.refl (stem (unary A) r).Leaf) (markerColorEquiv A)).bijective
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases x <;> rfl

lemma markerColorTarget_split (A : PrescribedTree n) (r : ℕ)
    (a : (stem (unary A) r).Leaf) (x y : Option (Fin (Fintype.card A.Leaf))) :
    splitDepth (stem (markerFork A) r) (markerColorTarget A r x) (markerColorTarget A r y)=
      splitDepth (stem (doubled A) r)
        (Option.elim' (markerOld A r a) (markerColorFresh A r) x)
        (Option.elim' (markerOld A r a) (markerColorFresh A r) y) := by
  have h := markerTarget_split A r a
    (Equiv.optionCongr (markerColorEquiv A) x) (Equiv.optionCongr (markerColorEquiv A) y)
  cases x <;> cases y <;> exact h

lemma marker_spatialProduct {Ω C D : Type} [Fintype Ω] [Fintype C] [Fintype D]
    (e : C ≃ D) (V : FinitePath Ω n → Fin N → ℝ) (x : Option C → FinitePath Ω n) :
    spatialProduct (fun c y i => match c with | none => 1 | some _ => V y i) x =
      spatialProduct (fun _ : D => V) (fun d => x (some (e.symm d))) := by
  classical
  unfold spatialProduct
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fintype.prod_option,one_mul]
  exact Fintype.prod_equiv e (fun c => V (x (some c)) i)
    (fun d => V (x (some (e.symm d))) i) (fun c => by simp)

/-- Concrete marker geometry at every preceding depth. In particular all
bijections and separation requirements of the history identity are produced,
not standing assumptions. The color count is positive for every tree. -/
theorem concrete_marker_covariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (A : PrescribedTree n) (r : ℕ) (a : (stem (unary A) r).Leaf)
    (K : (z : Z) → KernelTower (Ω z) (n+1+r)) (m : Fin (n+1+r+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last (n+1+r))=1)
    (V : (z : Z) → FinitePath (Ω z) (n+1+r) → Fin N → ℝ) :
    matrixRootCovariance μ Ω (stem (markerFork A) r) (stem (unary A) r)
      (markerColorTarget A r) K m
      (List.ofFn (fun c : Fin (Fintype.card A.Leaf) => (some c : Option (Fin (Fintype.card A.Leaf))))).reverse a
      (fun z => spatialProduct (fun c x i => match c with | none => 1 | some _ => V z x i))
      (fun z => treeOverlap (stem (unary A) r) (V z)) =
    partialKappa (stem (markerFork A) r) m (Finset.univ.image (markerColorTarget A r)) *
      ((∫ z, ((stem (doubled A) r).sampleLaw (K z)).expect (fun w =>
        spatialProduct (fun _ : (stem (unary A) r).Leaf => V z)
          (fun d => (stem (doubled A) r).pathAt (markerOld A r d) w) *
        spatialProduct (fun _ : (stem (unary A) r).Leaf => V z)
          (fun d => (stem (doubled A) r).pathAt
            (markerColorFresh A r ((markerColorOld A r).symm d)) w)) ∂μ) -
      (∫ z, ((stem (unary A) r).sampleLaw (K z)).expect
        (treeOverlap (stem (unary A) r) (V z)) ∂μ)^2) := by
  classical
  have h := marker_root_covariance μ Ω (stem (unary A) r) (stem (markerFork A) r)
    (stem (doubled A) r) a (markerColorOld A r) (markerColorTarget A r)
    (markerColorTarget_bijective A r) (markerOld A r) (markerColorFresh A r)
    (markerColorJoint_bijective A r) (markerOld_split A r)
    (fun c d => markerFresh_split A r (markerColorEquiv A c) (markerColorEquiv A d))
    (markerColorTarget_split A r a)
    (fun c d => marker_split_separation A r a d (markerColorEquiv A c)) K m hm hp hend
    ((List.ofFn (fun c : Fin (Fintype.card A.Leaf) => c)).reverse)
    (by
      rw [List.nodup_reverse, List.nodup_ofFn]
      exact Function.injective_id) (by
      ext c
      simp only [List.mem_toFinset,List.mem_reverse,List.mem_ofFn,Finset.mem_univ,iff_true]
      exact ⟨c,rfl⟩)
    (fun z => spatialProduct (fun _ : (stem (unary A) r).Leaf => V z))
  simp only [List.map_reverse,List.map_ofFn,Function.comp_def] at h
  simp_rw [← marker_spatialProduct (markerColorOld A r) (V _), ← treeOverlap_eq_spatialProduct] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext z x
  dsimp only [spatialProduct]
  congr 3
  funext i
  apply Finset.prod_congr rfl
  intro c hc
  cases c <;> rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

omit [Fintype Ω] in
lemma forkOverlap_paths (A : PrescribedTree n) (r : ℕ)
    (V : FinitePath Ω (n+1+r) → Fin N → ℝ) (j : Fin 2)
    (w : Sample Ω (stem (doubled A) r)) :
    forkOverlap A r V j w = spatialProduct (fun _ : A.Leaf => V)
      (fun a => (stem (doubled A) r).pathAt (stemLeaf (doubled A) r ⟨j,a⟩) w) := by
  induction r with
  | zero =>
    unfold forkOverlap treeOverlap spatialProduct
    congr 1
    apply Finset.sum_congr rfl
    intro _ _
    rw [leafProduct_eq_prod]
    rfl
  | succ r ih =>
    rw [forkOverlap,ih]
    rfl

lemma forkPairMean_zero (A : PrescribedTree n) (K : KernelTower Ω (n+1))
    (V : FinitePath Ω (n+1) → Fin N → ℝ) :
    forkPairMean A 0 K V = ((K.1.bind (fun x => A.sampleLaw (K.2 x))).expect
      (fun w => treeOverlap A (fun y => V (w.1,y)) w.2))^2 := by
  classical
  unfold forkPairMean
  change (FiniteLaw.pi (fun _ : Fin 2 => K.1.bind (fun x => A.sampleLaw (K.2 x)))).expect
    (fun w => treeOverlap A (fun y => V ((w 0).1,y)) (w 0).2 *
      treeOverlap A (fun y => V ((w 1).1,y)) (w 1).2)=_
  have h := FiniteLaw.expect_pi_pair (fun _ : Fin 2 => K.1.bind (fun x => A.sampleLaw (K.2 x)))
    0 1 (by decide) (fun x y => treeOverlap A (fun z => V (x.1,z)) x.2 * treeOverlap A (fun z => V (y.1,z)) y.2)
  refine h.trans ?_
  simp only [FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_right,pow_two]

lemma forkPairMean_succ (A : PrescribedTree n) (r : ℕ) (K : KernelTower Ω (n+1+r+1))
    (V : FinitePath Ω (n+1+r+1) → Fin N → ℝ) :
    forkPairMean A (r+1) K V = K.1.expect (fun x => forkPairMean A r (K.2 x) (fun y => V (x,y))) := by
  unfold forkPairMean
  exact sampleLaw_unary_expect (stem (doubled A) r) K
    (fun w => forkOverlap A r (fun y => V (w.1,y)) 0 w.2 * forkOverlap A r (fun y => V (w.1,y)) 1 w.2)

lemma unarySquareMean_succ (A : PrescribedTree n) (r : ℕ) (K : KernelTower Ω (n+1+r+1))
    (V : FinitePath Ω (n+1+r+1) → Fin N → ℝ) :
    unarySquareMean A (r+1) K V = K.1.expect (fun x => unarySquareMean A r (K.2 x) (fun y => V (x,y))) := by
  unfold unarySquareMean
  simp_rw [show ∀ w : Sample Ω (stem (unary A) (r+1)),
    treeOverlap (stem (unary A) (r+1)) V w = treeOverlap (stem (unary A) r) (fun y => V ((w 0).1,y)) (w 0).2
    from fun w => treeOverlap_unary _ V w]
  exact sampleLaw_unary_expect (stem (unary A) r) K
    (fun w => (treeOverlap (stem (unary A) r) (fun y => V (w.1,y)) w.2)^2)

lemma unarySquareMean_zero (A : PrescribedTree n) (K : KernelTower Ω (n+1))
    (V : FinitePath Ω (n+1) → Fin N → ℝ) :
    unarySquareMean A 0 K V=(K.1.bind (fun x => A.sampleLaw (K.2 x))).expect
      (fun w => (treeOverlap A (fun y => V (w.1,y)) w.2)^2) := by
  let F := fun w : Ω × Sample Ω A => (treeOverlap A (fun y => V (w.1,y)) w.2)^2
  have h := sampleLaw_unary_expect A K F
  have hh := FiniteLaw.expect_bind K.1 (fun x => A.sampleLaw (K.2 x)) F
  refine Eq.trans ?_ (h.trans hh.symm)
  apply FiniteLaw.expect_congr
  intro w
  exact congrArg (fun x : ℝ => x^2) (treeOverlap_unary A V w)

lemma marker_conditional_variance_zero (A : PrescribedTree n)
    (K : KernelTower Ω (n+1)) (V : FinitePath Ω (n+1) → Fin N → ℝ) :
    unarySquareMean A 0 K V - forkPairMean A 0 K V ≤ Real.sqrt (shapeEnergyAt A 0 K V) := by
  let P := K.1.bind (fun x => A.sampleLaw (K.2 x))
  let X := fun w : Ω × Sample Ω A => fun i => leafProduct A (fun y => V (w.1,y) i) w.2
  let R := fun w : Ω × Sample Ω A => treeOverlap A (fun y => V (w.1,y)) w.2
  have h := P.centered_contraction_bound X (fun _ => 1) (fun _ => by norm_num)
  have he (w : Ω × Sample Ω A) :
      FiniteLaw.dot (fun i => X w i-P.expect (fun y => X y i)) (fun _ => 1)=R w-P.expect R := by
    simp only [FiniteLaw.dot,mul_one,Finset.sum_sub_distrib,sub_div,R,treeOverlap,
      FiniteLaw.expect_div,FiniteLaw.expect_fintype_sum,X]
  simp_rw [he] at h
  rw [FiniteLaw.expect_sq_sub_expect] at h
  rw [forkPairMean_zero,unarySquareMean_zero]
  exact h

/-- Whole-shape conditional variance is controlled by the whole-shape
covariance energy. There is no missing projection or independence premise. -/
theorem marker_conditional_variance_le (A : PrescribedTree n) (r : ℕ)
    (K : KernelTower Ω (n+1+r)) (V : FinitePath Ω (n+1+r) → Fin N → ℝ) :
    unarySquareMean A r K V - forkPairMean A r K V ≤ Real.sqrt (shapeEnergyAt A r K V) := by
  induction r with
  | zero => exact marker_conditional_variance_zero A K V
  | succ r ih =>
    rw [unarySquareMean_succ,forkPairMean_succ,← FiniteLaw.expect_sub]
    apply (K.1.expect_mono (fun x => ih (K.2 x) (fun y => V (x,y)))).trans
    exact K.1.expect_sqrt_le _ (fun x => shapeEnergyAt_nonneg A r (K.2 x) (fun y => V (x,y)))

omit [Fintype Ω] in
lemma markerOld_overlap (A : PrescribedTree n) (r : ℕ)
    (V : FinitePath Ω (n+1+r) → Fin N → ℝ) (w : Sample Ω (stem (doubled A) r)) :
    spatialProduct (fun _ : (stem (unary A) r).Leaf => V)
      (fun a => (stem (doubled A) r).pathAt (markerOld A r a) w)=forkOverlap A r V 0 w := by
  rw [forkOverlap_paths]
  unfold spatialProduct
  congr 1
  apply Finset.sum_congr rfl
  intro _ _
  exact Fintype.prod_equiv (markerOldIndex A r) _ _ (fun a => rfl)

omit [Fintype Ω] in
lemma markerFresh_overlap (A : PrescribedTree n) (r : ℕ)
    (V : FinitePath Ω (n+1+r) → Fin N → ℝ) (w : Sample Ω (stem (doubled A) r)) :
    spatialProduct (fun _ : (stem (unary A) r).Leaf => V)
      (fun a => (stem (doubled A) r).pathAt (markerColorFresh A r ((markerColorOld A r).symm a)) w)=
      forkOverlap A r V 1 w := by
  rw [forkOverlap_paths]
  unfold spatialProduct
  congr 1
  apply Finset.sum_congr rfl
  intro _ _
  refine Fintype.prod_equiv (markerOldIndex A r) _ _ (fun a => ?_)
  have he : markerColorEquiv A ((markerColorOld A r).symm a)=markerOldIndex A r a := by
    change markerColorEquiv A ((markerColorEquiv A).symm (markerOldIndex A r a))=_
    exact (markerColorEquiv A).apply_symm_apply _
  simp only [markerColorFresh,Function.comp_apply,he,markerFresh]
  rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootOverlapVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
variable {Z : Type} [MeasurableSpace Z]

lemma mixedVariance_eq_centered (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ) :
    mixedVariance μ Ω P F = ∫ z, (P z).expect
      (fun w => (F z w-(∫ z, (P z).expect (F z) ∂μ))^2) ∂μ := by
  let c := ∫ z, (P z).expect (F z) ∂μ
  have he (z : Z) : (P z).expect (fun w => (F z w-c)^2)=
      (P z).expect (fun w => (F z w)^2) - 2*c*(P z).expect (F z)+c^2 := by
    calc
      _ = (P z).expect (fun w => (F z w)^2-(2*c)*F z w+c^2) :=
        (P z).expect_congr (fun w => by ring)
      _ = _ := by simp only [expect_add,expect_sub,expect_mul_left,expect_const]
  change _=∫ z, (P z).expect (fun w => (F z w-c)^2) ∂μ
  simp_rw [he]
  have hm : Integrable (fun z => 2*c*(P z).expect (F z)) μ := hF.const_mul (2*c)
  have hd : Integrable (fun z => (P z).expect (fun w => (F z w)^2)-2*c*(P z).expect (F z)) μ := hFsq.sub hm
  rw [integral_add hd (integrable_const _),
    integral_sub hFsq hm,integral_const_mul,integral_const]
  simp only [probReal_univ,one_smul]
  unfold mixedVariance
  dsimp only [c]
  ring

lemma mixedVariance_nonneg (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ) :
    0 ≤ mixedVariance μ Ω P F := by
  rw [mixedVariance_eq_centered μ Ω P F hF hFsq]
  exact integral_nonneg (fun z => (P z).expect_nonneg (fun _ => sq_nonneg _))

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable local instance rootOverlapVarianceDecidable_r802ef5_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- Root and prefix randomness are both retained. The square root is taken
only after integrating the actual conditional energy. -/
theorem overlapVariance_le_marker (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (A : PrescribedTree n) (r : ℕ)
    (K : (z : Z) → KernelTower (Ω z) (n+1+r))
    (V : (z : Z) → FinitePath (Ω z) (n+1+r) → Fin N → ℝ)
    (hsq : Integrable (fun z => unarySquareMean A r (K z) (V z)) μ)
    (hpair : Integrable (fun z => forkPairMean A r (K z) (V z)) μ)
    (hE : Integrable (fun z => shapeEnergyAt A r (K z) (V z)) μ)
    (hEs : Integrable (fun z => Real.sqrt (shapeEnergyAt A r (K z) (V z))) μ) :
    overlapVariance μ Ω (stem (unary A) r) K V ≤
      Real.sqrt (∫ z, shapeEnergyAt A r (K z) (V z) ∂μ)+|markerDefect μ Ω A r K V| := by
  have h := integral_mono (hsq.sub hpair) hEs
    (fun z => marker_conditional_variance_le A r (K z) (V z))
  simp only [Pi.sub_apply] at h
  rw [integral_sub hsq hpair] at h
  have he := integral_sqrt_le_sqrt_integral μ _ hE hEs (fun z => shapeEnergyAt_nonneg A r (K z) (V z))
  have hd := le_abs_self (markerDefect μ Ω A r K V)
  unfold overlapVariance FiniteLaw.mixedVariance markerDefect unarySquareMean at *
  linarith

lemma concrete_marker_covariance_eq_defect (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (A : PrescribedTree n) (r : ℕ) (a : (stem (unary A) r).Leaf)
    (K : (z : Z) → KernelTower (Ω z) (n+1+r)) (m : Fin (n+1+r+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last (n+1+r))=1)
    (V : (z : Z) → FinitePath (Ω z) (n+1+r) → Fin N → ℝ) :
    matrixRootCovariance μ Ω (stem (markerFork A) r) (stem (unary A) r)
      (markerColorTarget A r) K m
      (List.ofFn (fun c : Fin (Fintype.card A.Leaf) => (some c : Option (Fin (Fintype.card A.Leaf))))).reverse a
      (fun z => spatialProduct (fun c x i => match c with | none => 1 | some _ => V z x i))
      (fun z => treeOverlap (stem (unary A) r) (V z)) =
    partialKappa (stem (markerFork A) r) m (Finset.univ.image (markerColorTarget A r)) *
      markerDefect μ Ω A r K V := by
  have h := concrete_marker_covariance μ Ω A r a K m hm hp hend V
  simp_rw [markerOld_overlap,markerFresh_overlap] at h
  unfold markerDefect forkPairMean
  exact h

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootMarkerEstimate
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {n r M N : ℕ}

variable (A : PrescribedTree n)
    (T : KernelTower Ω (n+1+r)) (Q : (i : I) → Fin (n+1+r) → FiniteLaw (B i))
    (m : Fin (n+1+r) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+1+r) → ℝ)
    (old : (i : I) → FinitePath Ω (n+1+r) → FinitePath (B i) (n+1+r) → ℝ)
    (V : FinitePath Ω (n+1+r) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma root_unarySquareMean_eq (z : FullRootState Y X I M) :
    unarySquareMean A r (rootTower T Q m base old z) (rootVector V z) =
      rootTreeMean (stem (unary A) r) T Q m base old
        (fun x => (spatialProduct (fun _ : (stem (unary A) r).Leaf => V) x)^2) z := by
  unfold unarySquareMean rootTreeMean packRoot
  apply FiniteLaw.expect_congr
  intro w
  rw [treeOverlap_eq_spatialProduct]
  rfl

include hb hV in
lemma integrable_rootUnarySquareMean : Integrable (fun z : FullRootState Y X I M =>
    unarySquareMean A r (rootTower T Q m base old z) (rootVector V z)) μ := by
  simp_rw [root_unarySquareMean_eq]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1)
  intro x
  rw [abs_sq]
  exact (sq_le_one_iff_abs_le_one _).mpr (spatialProduct_bound _ (fun _ => hV) x)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma root_forkPairMean_eq (z : FullRootState Y X I M) :
    forkPairMean A r (rootTower T Q m base old z) (rootVector V z) =
      rootTreeMean (stem (doubled A) r) T Q m base old
        (fun x => spatialProduct (fun _ : A.Leaf => V)
          (fun a => x (stemLeaf (doubled A) r ⟨0,a⟩)) *
        spatialProduct (fun _ : A.Leaf => V)
          (fun a => x (stemLeaf (doubled A) r ⟨1,a⟩))) z := by
  unfold forkPairMean rootTreeMean packRoot
  apply FiniteLaw.expect_congr
  intro w
  simp only [forkOverlap_paths]
  rfl

include hb hV in
lemma integrable_rootForkPairMean : Integrable (fun z : FullRootState Y X I M =>
    forkPairMean A r (rootTower T Q m base old z) (rootVector V z)) μ := by
  simp_rw [root_forkPairMean_eq]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1)
  intro x
  rw [abs_mul]
  exact (mul_le_mul (spatialProduct_bound _ (fun _ => hV) _)
    (spatialProduct_bound _ (fun _ => hV) _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

include hb hV in
lemma integrable_rootSqrtShapeEnergy : Integrable (fun z : FullRootState Y X I M =>
    Real.sqrt (shapeEnergyAt A r (rootTower T Q m base old z) (rootVector V z))) μ := by
  apply Integrable.of_bound (measurable_rootShapeEnergy A r T Q m base old V hb).sqrt.aestronglyMeasurable 2
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_sqrt (shapeEnergyAt_le_four A r _ _ (fun y i => hV _ i))).trans_eq (by norm_num)

include hb hV in
 
theorem root_overlapVariance_le_marker [IsProbabilityMeasure μ] :
    overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) (stem (unary A) r)
      (rootTower T Q m base old) (rootVector V) ≤
      Real.sqrt (∫ z, shapeEnergyAt A r (rootTower T Q m base old z) (rootVector V z) ∂μ) +
      |markerDefect μ (rootAlphabet (Ω := Ω) (A := B)) A r
        (rootTower T Q m base old) (rootVector V)| := by
  exact overlapVariance_le_marker μ _ A r _ _
    (integrable_rootUnarySquareMean A T Q m base old V hb μ hV)
    (integrable_rootForkPairMean A T Q m base old V hb μ hV)
    (integrable_rootShapeEnergy A r T Q m base old V hb μ hV)
    (integrable_rootSqrtShapeEnergy A T Q m base old V hb μ hV)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalMarkerControl
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

lemma physicalShape_marker (hk : 0 < k) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) :
    physicalShapeCovariance m S a M C H N u (matrixSplitTest T q) false
      (spatialProduct (fun _ : S.Leaf => readVector
        (fun v x => readSpin (KernelTower.terminalState L x) v))) =
      physicalMarkerMatrixCovariance m S a M C H N u T q := by
  have hh := shapeCovariance_marker S a
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) T q
    (spatialProduct (fun _ : S.Leaf => readVector
      (fun v x => readSpin (KernelTower.terminalState L x) v)))
    (measurable_physicalBase M C H N) (fun j => (hm j).ne')
    (exponent_cons_monotone m (fun j => (hm j).le) hmono)
    (exponent_cons_nonneg m (fun j => (hm j).le)) (by simp) hend
    (by norm_num : (0:ℝ)≤1) (fun x => spatialProduct_bound _ (fun _ y i => readVector_bound _ y i) x)
    (fun _ : Fin N => M.field.toMeasure) (bondLaw M N) (markLaw (weights L) N)
    (M.alpha*N) (scoreRate N) hk
  refine hh.trans ?_
  unfold physicalMarkerMatrixCovariance markerMatrixCovariance
  congr 1
  funext z x
  rw [treeOverlap_eq_spatialProduct]
  rfl

lemma FullShapeControl.marker {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (k : ℕ) (hk : 0<k)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) :
    Tendsto (fun n => physicalMarkerMatrixCovariance (gridExponents L) S a M C H
      (Ns n+1) (us n) T q) atTop (𝓝 0) := by
  let F := fun n => spatialProduct (fun _ : S.Leaf =>
    readVector (fun v x => readSpin (KernelTower.terminalState L x) v) (N := Ns n+1))
  have hF : ∀ n x, |F n x|≤1 := fun n x => spatialProduct_bound _
    (fun _ y i => readVector_bound _ y i) x
  have hs := h.shape S a F 1 (by norm_num) hF k (matrixSplitTest T q) false
  simpa only [F,physicalShape_marker hk (gridExponents L) (gridExponents_pos L)
    (gridExponents_mono L) (gridExponents_last L)] using hs

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledMarkerEstimate
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory PrescribedTree
variable {Z : Type} [MeasurableSpace Z] {L N : ℕ}

lemma realize_marker_form (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d+1 ≤ q v) :
    realize (n+1+d) 0 S q = stem (unary (realize n (d+1) S q)) d := by
  rw [realize_stem (n+1) d 0 S q (fun v => by simpa using (hq v).trans' (Nat.le_succ d))]
  simp only [Nat.zero_add]
  rw [realize_unary_of_later n d S q (fun v => by have := hq v; omega)]

lemma scheduledMarkerDefect_eq_realize (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (e : L=n+1+d)
    (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) :
    scheduledMarkerDefect μ Ω d S q K V = markerDefect μ Ω (realize n (d+1) S q) d
      (fun z => kernelHeightCast e (K z)) (fun z => vectorHeightCast e (V z)) := by
  subst L
  unfold scheduledMarkerDefect
  rw [dite_eq_left (by omega : d<n+1+d)]
  have he (n' : ℕ) (hn : n'=n) (hc : n+1+d=n'+1+d) :
      markerDefect μ Ω (realize n' (d+1) S q) d
        (fun z => kernelHeightCast hc (K z)) (fun z => vectorHeightCast hc (V z)) =
      markerDefect μ Ω (realize n (d+1) S q) d K V := by
    subst n'
    rfl
  exact he _ (by omega) _

lemma scheduledOverlapVariance_eq_realize (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (e : L=n+1+d)
    (hq : ∀ v, d+1≤q v) (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) :
    scheduledOverlapVariance μ Ω S q K V =
      overlapVariance μ Ω (stem (unary (realize n (d+1) S q)) d)
        (fun z => kernelHeightCast e (K z)) (fun z => vectorHeightCast e (V z)) := by
  subst L
  unfold scheduledOverlapVariance
  rw [realize_marker_form n d S q hq]
  rfl

end DilutedSpinGlass.ReducedTopology
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PrescribedTree ReducedTopology
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (B i))
    (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (B i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

include hb hV in
lemma root_scheduled_variance_le_marker (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (e : L=n+1+d) (hq : ∀ v, d+1≤q v) :
    scheduledOverlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S q
      (rootTower T Q m base old) (rootVector V) ≤
      Real.sqrt (∫ z, scheduledShapeEnergy L d S q (rootTower T Q m base old z) (rootVector V z) ∂μ) +
      |scheduledMarkerDefect μ (rootAlphabet (Ω := Ω) (A := B)) d S q
        (rootTower T Q m base old) (rootVector V)| := by
  subst L
  rw [scheduledOverlapVariance_eq_realize μ _ n d S q rfl hq,
    scheduledMarkerDefect_eq_realize μ _ n d S q rfl]
  simp_rw [scheduledShapeEnergy_eq_realize n d S q rfl]
  exact root_overlapVariance_le_marker (realize n (d+1) S q) T Q m base old V hb μ hV

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerScheduledIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory PrescribedTree
variable {Z : Type} [MeasurableSpace Z] {L N : ℕ}

noncomputable local instance markerScheduledIdentityDecidableEq_r802ef5_1 (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
lemma scheduledMarkerDefect_covariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (e : L=n+1+d)
    (K : (z : Z) → KernelTower (Ω z) L) (m : Fin (L+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last L)=1)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) :
    let A := realize n (d+1) S q
    let S' := stem (unary A) d
    let T' := stem (markerFork A) d
    let a := firstLeaf S'
    let q' := markerColorTarget A d
    markerMatrixCovariance μ Ω (heightCast e.symm S') (leafHeightCast e.symm S' a)
      (heightCast e.symm T') (fun c => leafHeightCast e.symm T' (q' c)) K m V =
      partialKappa T' (fun j => m (Fin.cast (congrArg (fun a => a+1) e.symm) j))
        (Finset.univ.image q') * scheduledMarkerDefect μ Ω d S q K V := by
  subst L
  dsimp only [heightCast,leafHeightCast,Fin.cast]
  rw [scheduledMarkerDefect_eq_realize μ Ω n d S q rfl]
  unfold markerMatrixCovariance
  convert concrete_marker_covariance_eq_defect μ Ω (realize n (d+1) S q) d
      (firstLeaf (stem (unary (realize n (d+1) S q)) d)) K m hm hp hend V using 1 <;> congr 3
  funext z x
  unfold spatialProduct
  congr 2
  funext i
  apply Finset.prod_congr rfl
  intro color _
  cases color <;> rfl

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_OverlapDepthAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance overlapDepthAverageDecidableEq_r802ef5_1 (β : Type) :
    DecidableEq β := Classical.decEq β
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.overlapDepthAveragePropDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_option (D : (Option α → Fin L) → Prop) (F : (Option α → Fin L) → ℝ) :
    average D F=(FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
      average (fun q => D ((fun i => Option.elim i t q))) (fun q => F ((fun i => Option.elim i t q)))) := by
  rw [average_split none D F]
  apply FiniteLaw.expect_congr
  intro t
  let e : α → {j : Option α // j≠none} := fun i => ⟨some i,by simp⟩
  have he : Function.Injective e := by intro a b hab; exact Option.some_injective _ (congrArg Subtype.val hab)
  have hi (rest : {j : Option α // j≠none} → Fin L) :
      insertCoordinate none t rest=(fun i => Option.elim i t (coordinateProjection e (fun _ => Equiv.refl _) rest)) := by
    funext i
    cases i with
    | none => exact insertCoordinate_self _ _ _
    | some a => exact insertCoordinate_other none t rest (e a)
  unfold average
  simp_rw [hi]
  exact depthLaw_projection e he (fun _ => Equiv.refl _)
    (fun q => if D ((fun i => Option.elim i t q)) then F ((fun i => Option.elim i t q)) else 0)

lemma average_option_product (D : (α → Fin L) → Prop) (E : Fin L → Prop)
    (F : (α → Fin L) → ℝ) :
    average (fun Q : Option α → Fin L => D (fun i => Q (some i)) ∧ E (Q none))
      (fun Q => F (fun i => Q (some i))) =
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t => if E t then 1 else 0) * average D F := by
  rw [average_option]
  have he (t : Fin L) :
      average (fun q : α → Fin L => D q ∧ E t) F=(if E t then 1 else 0)*average D F := by
    by_cases ht : E t
    · simp [ht]
    · simp [ht,average]
  simp only [Option.elim_some,Option.elim_none,he]
  exact (FiniteLaw.expect_mul_right _ _ _)

lemma uniform_interval (r : ℕ) (hr : 2*r<L) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t => if r<t.val ∧ t.val≤2*r then (1:ℝ) else 0) =
      (r:ℝ)/(L:ℝ) := by
  unfold FiniteLaw.expect FiniteLaw.uniform
  rw [← Finset.mul_sum]
  have he : (Finset.univ.filter (fun t : Fin L => r<t.val ∧ t.val≤2*r)).card=r := by
    have hv : Finset.univ.filter (fun t : Fin L => r<t.val ∧ t.val≤2*r)=
        Finset.Ioc (⟨r,by omega⟩ : Fin L) ⟨2*r,hr⟩ := by ext t; simp [Fin.lt_def,Fin.le_def]
    rw [hv]
    simp
    omega
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,Fintype.card_fin,nsmul_eq_mul,mul_one,he]
  rw [div_eq_mul_inv,mul_comm]

end DilutedSpinGlass.DepthAverage

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularOverlapGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage
noncomputable local instance regularOverlapGeometryDecidableEq_r802ef5_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance regularOverlapGeometryPropDecidable_r802ef5_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {L : ℕ} [NeZero L]

lemma admissible_of_all_lower (S : ReducedTopology) (q : S.Vertex → ℕ) {lo lo' hi : ℕ}
    (h : Admissible S q lo hi) (hl : ∀ v, lo'≤q v) : Admissible S q lo' hi := by
  cases S with
  | leaf => trivial
  | node k hk C => exact ⟨hl none,h.2⟩

omit [NeZero L] in
lemma regular_prepend {α : Type} {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (q : α → Fin L) (hq : Regular η q) (d : Fin L)
    (hlo : η/4<normalized d) (hhi : normalized d≤η/2) :
    Regular (η/8) (fun i : Option α => i.elim d q) := by
  constructor
  · intro i
    cases i with
    | none => simp only [Option.elim_none]; constructor <;> linarith
    | some i => simpa only [Option.elim_some] using
        (show η/8<normalized (q i) ∧ normalized (q i)<1-η/8 by have := hq.1 i; constructor <;> linarith)
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        simp only [Option.elim_none,Option.elim_some]
        have hj := (hq.1 j).1
        rw [abs_of_neg (by linarith : normalized d-normalized (q j)<0)]
        linarith
    | some i =>
      cases j with
      | none =>
        simp only [Option.elim_none,Option.elim_some]
        have hi := (hq.1 i).1
        rw [abs_of_pos (by linarith : 0<normalized (q i)-normalized d)]
        linarith
      | some j =>
        have hh := hq.2 i j (by intro e; exact hij (congrArg some e))
        simp only [Option.elim_some]
        linarith

lemma regularOverlap_prepend {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (S : ReducedTopology) (q : S.Vertex → Fin L) (hq : regularOverlapDomain S L η q)
    (d : Fin L) (hlo : η/4<normalized d) (hhi : normalized d≤η/2) :
    regularShapeDomain S L (η/8) (fun i => i.elim d q) := by
  refine ⟨regular_prepend hη hη1 q hq.1 d hlo hhi,?_⟩
  apply admissible_of_all_lower S _ hq.2
  intro v
  have hh : normalized d<normalized (q v) := by have := (hq.1.1 v).1; linarith
  have he : d.val<(q v).val := by
    unfold normalized at hh
    exact_mod_cast ((div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr (NeZero.pos L))).mp hh)
  simpa only [Option.elim_some,Option.elim_none] using (Nat.succ_le_of_lt he)

lemma overlap_interval_geometry {η : ℝ} (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L:ℝ)) :
    let r := ⌊η*(L:ℝ)/4⌋₊
    2*r<L ∧ η/8≤(r:ℝ)/(L:ℝ) ∧
      ∀ d : Fin L, r<d.val ∧ d.val≤2*r → η/4<normalized d ∧ normalized d≤η/2 := by
  let r := ⌊η*(L:ℝ)/4⌋₊
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hr : (r:ℝ)≤η*(L:ℝ)/4 := Nat.floor_le (by positivity)
  have hrs : η*(L:ℝ)/4<(r:ℝ)+1 := Nat.lt_floor_add_one _
  have h2r : (2*r:ℕ)<L := by
    have hh : (2:ℝ)*(r:ℝ)<(L:ℝ) := by nlinarith
    exact_mod_cast hh
  refine ⟨h2r,(le_div_iff₀ hL).mpr (by nlinarith),?_⟩
  intro d hd
  have hd0 : (r:ℝ)+1≤(d.val:ℝ) := by exact_mod_cast hd.1
  have hd1 : (d.val:ℝ)≤2*(r:ℝ) := by exact_mod_cast hd.2
  constructor
  · exact (lt_div_iff₀ hL).mpr (by nlinarith)
  · exact (div_le_iff₀ hL).mpr (by nlinarith)

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalOverlapConcentration
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
variable {L p : ℕ}

noncomputable local instance physicalOverlapConcentrationDictionaryDecidableEq_r802ef5_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma FullShapeControl.markerDefect {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) :
    Tendsto (fun t => physicalMarkerDefect M C H (Ns t+1) L (us t) S Q) atTop (𝓝 0) := by
  let d := (Q none).val
  let n := L-d
  have e : L+1=n+1+d := by dsimp [n,d]; have := (Q none).isLt; omega
  let A := realize n (d+1) S (fun v => (Q (some v)).val)
  let S' := stem (unary A) d
  let T' := stem (markerFork A) d
  let a := firstLeaf S'
  let q := markerColorTarget A d
  let m : Fin (n+1+d+1) → ℝ := fun j =>
    (Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) (Fin.cast (congrArg (fun a => a+1) e.symm) j)
  let κ := partialKappa T' m (Finset.univ.image q)
  have hm : StrictMono m := by
    intro i j hij
    dsimp [m]
    rw [gridExponents_cons]
    apply (grid_strictMono (by omega : 0<L+1))
    simpa only [Fin.cast_lt_cast] using hij
  have hp : ∀ j, 0 ≤ m j := by
    intro j
    dsimp [m]
    rw [gridExponents_cons]
    exact grid_nonneg _
  have hend : m (Fin.last (n+1+d))=1 := by
    dsimp [m]
    simp only [Fin.cast_last]
    rw [gridExponents_cons]
    exact grid_last (by omega)
  have hκ : κ≠0 := partialKappa_ne_zero T' m hm hp _
  have hcard : 0<Fintype.card A.Leaf := by
    have : Nonempty A.Leaf := ⟨firstLeaf A⟩
    exact Fintype.card_pos
  have ht := h.marker (heightCast e.symm S') (leafHeightCast e.symm S' a)
    (Fintype.card A.Leaf) hcard (heightCast e.symm T') (fun c => leafHeightCast e.symm T' (q c))
  have heq (t : ℕ) : physicalMarkerMatrixCovariance (gridExponents L)
      (heightCast e.symm S') (leafHeightCast e.symm S' a) M C H (Ns t+1) (us t)
      (heightCast e.symm T') (fun c => leafHeightCast e.symm T' (q c)) =
      κ * physicalMarkerDefect M C H (Ns t+1) L (us t) S Q := by
    unfold physicalMarkerMatrixCovariance physicalMarkerDefect
    exact scheduledMarkerDefect_covariance _ _ n d S _ e _ (Fin.cons 0 (gridExponents L))
      (by rw [gridExponents_cons]; exact grid_strictMono (by omega))
      (by rw [gridExponents_cons]; exact grid_nonneg)
      (by rw [gridExponents_cons]; exact grid_last (by omega)) _
  have hx : Tendsto (fun t => κ*physicalMarkerDefect M C H (Ns t+1) L (us t) S Q) atTop (𝓝 0) := by
    simpa only [heq] using ht
  have hh := hx.div_const κ
  simpa only [mul_div_cancel_left₀ _ hκ,zero_div] using hh

lemma physicalOverlapVariance_le_marker (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1))
    (hq : ∀ v, (Q none).val+1≤(Q (some v)).val) :
    physicalOverlapVariance M C H N L u S (fun v => Q (some v)) ≤
      Real.sqrt (physicalScheduledEnergy M C H N L u S Q)+|physicalMarkerDefect M C H N L u S Q| := by
  unfold physicalOverlapVariance physicalScheduledEnergy physicalMarkerDefect
  exact root_scheduled_variance_le_marker _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i) (L-(Q none).val) (Q none).val S _
    (by have := (Q none).isLt; omega) hq

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance physicalOverlapConcentrationAverageDecidableEq_r802ef5_1 (type : Type) :
    DecidableEq type := Classical.decEq type
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.physicalOverlapConcentrationAverageDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_domain_bound (D E : (α → Fin L) → Prop) (F G : (α → Fin L) → ℝ)
    (hDE : ∀ q, D q → E q) (hFG : ∀ q, D q → F q≤G q) (hG : ∀ q, 0≤G q) :
    average D F≤average E G := by
  apply FiniteLaw.expect_mono
  intro q
  by_cases hd : D q
  · rw [ite_eq_left hd,ite_eq_left (hDE q hd)]
    exact hFG q hd
  · rw [ite_eq_right hd]
    split_ifs
    · exact hG q
    · rfl

lemma average_option_interval_bound (r : ℕ) (hr : 2*r<L) (c : ℝ) (hc : c≤(r:ℝ)/(L:ℝ))
    (A : (α → Fin L) → Prop) (B : (Option α → Fin L) → Prop)
    (F : (α → Fin L) → ℝ) (E D : (Option α → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) (hE : ∀ Q, 0≤E Q) (hD : ∀ Q, 0≤D Q)
    (hsub : ∀ Q, A (fun v => Q (some v)) ∧ r<(Q none).val ∧ (Q none).val≤2*r → B Q)
    (hpoint : ∀ Q, B Q → F (fun v => Q (some v))≤Real.sqrt (E Q)+D Q) :
    c*average A F≤Real.sqrt (average B E)+average B D := by
  let I := fun Q : Option α → Fin L => A (fun v => Q (some v)) ∧ r<(Q none).val ∧ (Q none).val≤2*r
  have hav : average I (fun Q => F (fun v => Q (some v)))=((r:ℝ)/(L:ℝ))*average A F := by
    have hh := average_option_product A (fun t : Fin L => r<t.val ∧ t.val≤2*r) F
    calc
      _ = _ := hh
      _ = _ := congrArg (fun x : ℝ => x*average A F) (by
        convert uniform_interval r hr using 1
        all_goals try with_reducible_and_instances rfl
        apply FiniteLaw.expect_congr
        intro t
        split_ifs <;> rfl)
  calc
    _ ≤ ((r:ℝ)/(L:ℝ))*average A F := mul_le_mul_of_nonneg_right hc (average_nonneg _ _ hF)
    _ = average I (fun Q => F (fun v => Q (some v))) := hav.symm
    _ ≤ average B (fun Q => Real.sqrt (E Q)+D Q) :=
      average_domain_bound I B _ _ hsub (fun Q hQ => hpoint Q (hsub Q hQ))
        (fun Q => add_nonneg (Real.sqrt_nonneg _) (hD Q))
    _ = average B (fun Q => Real.sqrt (E Q))+average B D := average_add_eq _ _ _
    _ ≤ _ := add_le_add (average_sqrt_le B E hE) le_rfl

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.physicalOverlapConcentrationTopologyDecidableEq
noncomputable local instance physicalOverlapConcentrationTopologyDecidable_r802ef5_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {L : ℕ} [NeZero L]

/-- A positive fraction of early marker prefixes transfers the covariance
estimate without a mesh-size penalty or a diagonal depth restriction. -/
theorem regular_overlap_average_bound (S : ReducedTopology) {η : ℝ}
    (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L:ℝ))
    (F : (S.Vertex → Fin L) → ℝ) (E D : (Option S.Vertex → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) (hE : ∀ Q, 0≤E Q) (hD : ∀ Q, 0≤D Q)
    (hpoint : ∀ Q, regularShapeDomain S L (η/8) Q →
      F (fun v => Q (some v))≤Real.sqrt (E Q)+D Q) :
    (η/8)*average (regularOverlapDomain S L η) F ≤
      Real.sqrt (average (regularShapeDomain S L (η/8)) E)+
      average (regularShapeDomain S L (η/8)) D := by
  have hg := overlap_interval_geometry hη hη1 hlarge
  apply average_option_interval_bound _ hg.1 _ hg.2.1
    (regularOverlapDomain S L η) (regularShapeDomain S L (η/8)) F E D hF hE hD _ hpoint
  intro Q hQ
  have hd := hg.2.2 (Q none) hQ.2
  have hh := regularOverlap_prepend hη hη1 S (fun v => Q (some v)) hQ.1 (Q none) hd.1 hd.2
  have he : (fun i : Option S.Vertex => i.elim (Q none) (fun v => Q (some v)))=Q := by
    funext i; cases i <;> rfl
  rwa [he] at hh

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootOverlapBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (B i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (B i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma root_overlapMoment_eq [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] (j : ℕ) (z : FullRootState Y X I M) :
    (S.sampleLaw (rootTower T Q m base old z)).expect (fun w => (treeOverlap S (rootVector V z) w)^j) =
    rootTreeMean S T Q m base old (fun x => (spatialProduct (fun _ : S.Leaf => V) x)^j) z := by
  unfold rootTreeMean packRoot
  apply FiniteLaw.expect_congr
  intro w
  rw [treeOverlap_eq_spatialProduct]
  rfl

include hb hV in
lemma integrable_rootOverlapMoment (j : ℕ) : Integrable (fun z : FullRootState Y X I M =>
    (S.sampleLaw (rootTower T Q m base old z)).expect (fun w => (treeOverlap S (rootVector V z) w)^j)) μ := by
  simp_rw [root_overlapMoment_eq]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1)
  intro x
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (spatialProduct_bound _ (fun _ => hV) x)

include hb hV in
lemma root_overlapVariance_nonneg :
    0 ≤ overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V) := by
  apply FiniteLaw.mixedVariance_nonneg
  · simpa using integrable_rootOverlapMoment S T Q m base old V hb μ hV 1
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalOverlapAverage
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

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapAverageDecidableEq
lemma physicalOverlapVariance_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (q : S.Vertex → Fin (L+1)) :
    0≤physicalOverlapVariance M C H N L u S q := by
  unfold physicalOverlapVariance scheduledOverlapVariance
  exact root_overlapVariance_nonneg _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

lemma physicalOverlapAverage_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalOverlapAverage M C H N L u S η :=
  DepthAverage.average_nonneg _ _ (physicalOverlapVariance_nonneg M C H N L u S)

lemma physicalOverlapAverage_le_marker (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) {η : ℝ}
    (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L+1:ℕ)) :
    (η/8)*physicalOverlapAverage M C H N L u S η≤
      Real.sqrt (physicalShapeAverage M C H N L u S (η/8))+
      DepthAverage.average (regularShapeDomain S (L+1) (η/8))
        (fun Q => |physicalMarkerDefect M C H N L u S Q|) := by
  apply regular_overlap_average_bound S hη hη1 hlarge
    (physicalOverlapVariance M C H N L u S) (physicalScheduledEnergy M C H N L u S)
    (fun Q => |physicalMarkerDefect M C H N L u S Q|)
    (physicalOverlapVariance_nonneg M C H N L u S)
    (physicalScheduledEnergy_nonneg M C H N L u S) (fun _ => abs_nonneg _) ?_
  intro Q hQ
  apply physicalOverlapVariance_le_marker
  intro v
  exact admissible_lower S _ hQ.2 v

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalOverlapLimit
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

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimitDecidableEq
lemma physicalOverlapLimsup_bound_oai {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : ReducedTopology) {η : ℝ} (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L+1:ℕ)) :
    (η/8)*physicalOverlapLimsup M C H L Ns us S η≤
      Real.sqrt (physicalShapeLimsup M C H L Ns us S (η/8)) := by
  have he : Tendsto (fun n => DepthAverage.average (regularShapeDomain S (L+1) (η/8))
      (fun Q => |physicalMarkerDefect M C H (Ns n+1) L (us n) S Q|)) atTop (𝓝 0) := by
    apply DepthAverage.tendsto_average_zero
    intro Q
    simpa only [abs_zero] using (h.markerDefect S Q).abs
  apply limsup_sqrt_error_bound _ _ _ (by positivity)
    (fun n => physicalOverlapAverage_nonneg M C H (Ns n+1) L (us n) S η)
    (fun n => physicalShapeAverage_le_one M C H (Ns n+1) L (us n) S (η/8)) he
  intro n
  exact physicalOverlapAverage_le_marker M C H (Ns n+1) L (us n) S hη hη1 hlarge

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound_oai := @OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound_oai
