-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:08:13.977281+00:00
-- url     : https://prove2.me/submissions/9ba9c647-79d5-459c-a9e7-1ef7ec70f484

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physicalOverlapLimsup_bound
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physicalShapeLimsup_tendsto

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

noncomputable local instance instDecidable_4_r6b90f8_1 (p : Prop) : Decidable p := Classical.propDecidable p
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

noncomputable local instance treeMarkLawPropDecidable_r6b90f8_1 (proposition : Prop) :
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


noncomputable local instance instDecidableEqEdge_r6b90f8_1 {n : ℕ} (S : PrescribedTree n) : DecidableEq (Edge S) := Classical.decEq _
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
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

end DilutedSpinGlass

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

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SplitDepthContinuity
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinRootData
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

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
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualNegligible
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
open scoped Topology BigOperators

lemma limsup_finite_linear_bound {ι : Type*} (s : Finset ι)
    (a : ℕ → ℝ) (f : ι → ℕ → ℝ) (c e : ι → ℝ)
    (hc : ∀ i∈s, 0 ≤ c i) (ha0 : ∀ n, 0 ≤ a n)
    (hf1 : ∀ i∈s, ∀ n, f i n ≤ 1)
    (hbound : ∀ n, a n ≤ ∑ i∈s, c i*(f i n+e i)) :
    limsup a atTop ≤ ∑ i∈s, c i*(limsup (f i) atTop+e i) := by
  classical
  have hcap (t : ℝ) (ht : 0<t) :
      limsup a atTop ≤ ∑ i∈s, c i*(limsup (f i) atTop+t+e i) := by
    have hff : ∀ᶠ n in atTop, ∀ i∈s, f i n<limsup (f i) atTop+t := by
      apply (eventually_all_finite s.finite_toSet).mpr
      intro i hi
      exact eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht)
        (isBoundedUnder_of_eventually_le (Eventually.of_forall (hf1 i hi)))
    apply limsup_le_of_le
      (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha0).frequently))
    filter_upwards [hff] with n hn
    apply (hbound n).trans
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (add_le_add (hn i hi).le le_rfl) (hc i hi))
  have hcont : ContinuousAt (fun t : ℝ => ∑ i∈s, c i*(limsup (f i) atTop+t+e i)) 0 := by
    fun_prop
  have ht : Tendsto (fun t : ℝ => ∑ i∈s, c i*(limsup (f i) atTop+t+e i)) (𝓝[>] 0)
      (𝓝 (∑ i∈s, c i*(limsup (f i) atTop+e i))) := by
    simpa using hcont.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun t ht => hcap t ht))

/-- First take each fixed-grid limsup, then the grid limit, and only then
let the arbitrary regularity cutoff tend to zero. -/
lemma squeeze_triangle_grid_zero (a : ℕ → ℝ) (C : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hC : 0 ≤ C) (b : ℝ → ℕ → ℝ)
    (hb : ∀ η, 0<η → Tendsto (b η) atTop (𝓝 (C*η)))
    (hbound : ∀ η, 0<η → ∀ n, a n ≤ b η n) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε/(2*(C+1))
  have hη : 0<η := div_pos hε (by positivity)
  have hcut : C*η<ε := by
    dsimp [η]
    have h : C/(2*(C+1))<1 := (div_lt_one (by positivity)).mpr (by linarith)
    calc
      C*(ε/(2*(C+1))) = ε*(C/(2*(C+1))) := by ring
      _ < ε*1 := mul_lt_mul_of_pos_left h hε
      _ = ε := mul_one ε
  obtain ⟨n,hn⟩ := (eventually_atTop.mp ((hb η hη).eventually (Iio_mem_nhds hcut)))
  refine ⟨n,fun m hm => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (ha m)]
  exact (hbound η hη m).trans_lt (hn m hm)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TripleMarginal
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullThermalAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

noncomputable local instance pairObservableHistoryDecidable_r6b90f8_1 (proposition : Prop) :
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PairSquare
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

noncomputable local instance pairSiteAverageDecidable_r6b90f8_1 (proposition : Prop) :
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

noncomputable local instance pairSquareDecidable_r6b90f8_1 (proposition : Prop) :
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullTreeScore
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_GeneralPairSquare
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

noncomputable local instance generalPairSquareDecidable_r6b90f8_1 (proposition : Prop) :
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
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n : ℕ}

noncomputable local instance matrixPairRegularityPropDecidable_r6b90f8_1 (proposition : Prop) : Decidable proposition :=
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalTaylor
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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

noncomputable local instance matrixEnergyPropDecidable_r6b90f8_1 (proposition : Prop) :
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

noncomputable local instance kappaLowerDecidable_r6b90f8_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
lemma leaf_nonempty {n : ℕ} (S : PrescribedTree n) : Nonempty S.Leaf := by
  induction S with
  | leaf => exact ⟨()⟩
  | @node n k C ih =>
    obtain ⟨a⟩ := ih ⟨0,k.property⟩
    exact ⟨⟨⟨0,k.property⟩,a⟩⟩

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

lemma leaves_unary {n : ℕ} (S : PrescribedTree n) : leaves (unary S) = leaves S := by
  change (∑ _ : Fin 1, leaves S) = _
  simp

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

/-- Actual vertex multiplicities, with assigned *absolute* depths. Aligned
copies may repeat a coordinate but never merge their branching vertices. -/
theorem realize_branchingCount (r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : Admissible S q d (d+r)) (P : ℕ → Prop) :
    PrescribedTree.branchingCount (realize r d S q) (fun u => P (d+u)) =
      ∑ v : S.Vertex, if P (q v) then 1 else 0 := by
  classical
  induction r generalizing d S with
  | zero =>
    cases S with
    | leaf => exact (Finset.sum_empty).symm
    | node k hk C => have := h.2.1; have := h.1; omega
  | succ r ih =>
    cases S with
    | leaf =>
      rw [realize,PrescribedTree.branchingCount_unary]
      have hh := ih (d+1) .leaf q trivial
      convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]
    | node k hk C =>
      rw [realize]
      split_ifs with hd
      · rw [PrescribedTree.branchingCount_unary]
        have ha : Admissible (.node k hk C) q (d+1) ((d+1)+r) :=
          ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩
        have hh := ih (d+1) (.node k hk C) q ha
        convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]
      · have he : q none=d := by have := h.1; omega
        change _ = ∑ v : Option ((i : Fin k) × (C i).Vertex), _
        rw [Fintype.sum_option,Fintype.sum_sigma]
        simp only [PrescribedTree.branchingCount,Nat.add_zero,show 1<(k:ℕ) by omega,and_true,he]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have ha : Admissible (C i) (fun v => q (some ⟨i,v⟩)) (d+1) ((d+1)+r) := by
          simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2.2 i
        have hh := ih (d+1) (C i) (fun v => q (some ⟨i,v⟩)) ha
        convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]

end ReducedTopology
end DilutedSpinGlass
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

noncomputable local instance shapeMatrixPropDecidable_r6b90f8_1 (proposition : Prop) :
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

lemma matrix_history_spatialProduct_same (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (K : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (D : FinitePath Ω (L+1) → Fin N → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (f : Sample Ω S → ℝ) :
    matrixObservableHistory T q K m
      (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a (spatialProduct (fun _ => D)) f =
      (∑ i : Fin N, shapeHistory K m (matrixSplitTest T q)
        (fun c x => match c with | none => if true = true then D x i else 1 | some _ => D x i) S a f)/(N:ℝ) := by
  rw [matrix_history_spatialProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext c x
  cases c <;> rfl

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

/-- Fix all child coordinates first, then average the evaluation coordinate. -/
lemma average_split_comm (a : α) (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) :
    average D F=(depthLaw {j : α // j≠a} L).expect (fun rest =>
      (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
        if D (insertCoordinate a t rest) then F (insertCoordinate a t rest) else 0)) := by
  rw [average_split a D F]
  exact FiniteLaw.expect_comm _ _ _

end DilutedSpinGlass.DepthAverage
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalPairEnergy
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalSingleton
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullCubeConditionalContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma integral_rootShapeHistory_matrix (z : FullRootState Y X (Labels L (Site N)) M) :
    (∫ i, rootShapeHistory S a K m base old read (matrixSplitTest T q) true f z i ∂siteLaw N) =
      rootMatrixObservable S a K m base old read T q f z := by
  rw [integral_siteLaw]
  symm
  exact matrix_history_spatialProduct_same T q
    (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old z) m
    (rootVector (readVector read) z) S a
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

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

lemma shapeAverage_matrix (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) (hk : 0 < k) :
    shapeAverage ξ μ ν (siteLaw N) rate score S a K m base old read (matrixSplitTest T q) true f =
      ∫ z, rootMatrixObservable S a K m base old read T q f z ∂fullRootLaw ξ μ ν rate score := by
  unfold shapeAverage
  rw [integral_prod _ (integrable_rootShapeHistory_general S a K m base old read f
    hb hm hmono hpos hroot hend hB hf ξ μ ν rate score hk (matrixSplitTest T q) true)]
  exact integral_congr_ae (ae_of_all _ (fun z => integral_rootShapeHistory_matrix S a K m base old read T q f z))

lemma shapeCovariance_matrix (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0) (hk : 0 < k) :
    shapeCovariance ξ μ ν (siteLaw N) rate score S a K m base old read (matrixSplitTest T q) true f =
      matrixRootCovariance (fullRootLaw ξ μ ν rate score)
        (rootAlphabet (Ω := Ω) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
        (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old) m
        (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse a
        (fun z => spatialProduct (fun _ => rootVector (readVector read) z))
        (fun z x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x))) := by
  unfold shapeCovariance
  rw [shapeAverage_matrix S a K m base old read T q f hb hm hmono hpos hroot hend hB hf
    ξ μ ν rate score hk,
    shapeAverage_matrix S a K m base old read T q (fun _ => 1) hb hm hmono hpos hroot hend
    (by norm_num : (0:ℝ) ≤ 1) (fun _ => by simp) ξ μ ν rate score hk]
  rfl

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixPhysical
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
variable {L p k : ℕ}

lemma physicalShape_matrix (hk : 0 < k) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    physicalShapeCovariance m S a M C H N u (matrixSplitTest T q) true f =
      physicalMatrixCovariance m S a M C H N u T q f := by
  exact shapeCovariance_matrix S a
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) T q f
    (measurable_physicalBase M C H N) (fun j => (hm j).ne')
    (exponent_cons_monotone m (fun j => (hm j).le) hmono)
    (exponent_cons_nonneg m (fun j => (hm j).le)) (by simp) hend hB hf
    (fun _ : Fin N => M.field.toMeasure) (bondLaw M N) (markLaw (weights L) N)
    (M.alpha*N) (scoreRate N) hk

end DilutedSpinGlass.UniversalDictionary
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalTreeMatrix
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
variable {L p k : ℕ}

lemma physicalTreeMatrixCovariance_eq (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) :
    physicalTreeMatrixCovariance m S a M C H N u T q =
      physicalMatrixCovariance m S a M C H N u T q
        (spatialProduct (fun _ : S.Leaf =>
          readVector (fun v x => readSpin (KernelTower.terminalState L x) v))) := by
  unfold physicalTreeMatrixCovariance physicalMatrixCovariance
  congr 1
  funext z x
  rw [treeOverlap_eq_spatialProduct]
  rfl

end DilutedSpinGlass.UniversalDictionary
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
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledSingleton
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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

omit [Fintype Ω] in
lemma leafProduct_singleton (C : PrescribedTree n) [Subsingleton C.Leaf] (a : C.Leaf)
    (f : FinitePath Ω n → ℝ) (z : Sample Ω C) : leafProduct C f z=f (C.pathAt a z) := by
  rw [leafProduct_eq_prod,Fintype.prod_subsingleton _ a]

lemma childEnergy_singleton (C : PrescribedTree n) (hC : Fintype.card C.Leaf=1)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ) :
    childEnergy C T f=(KernelTower.law (n+1) T).covarianceEnergy f := by
  let : Subsingleton C.Leaf := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨a⟩ := leaf_nonempty C
  rcases T with ⟨μ,K⟩
  unfold childEnergy FiniteLaw.covarianceEnergy FiniteLaw.covariance
  simp_rw [leafProduct_singleton C a]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  erw [branch_leaf_marginal C μ K a (fun w => f w i * f w j),
    branch_leaf_marginal C μ K a (fun w => f w i),
    branch_leaf_marginal C μ K a (fun w => f w j)]

lemma shapeEnergyAt_singleton (C : PrescribedTree n) (hC : Fintype.card C.Leaf=1)
    (d : ℕ) (T : KernelTower Ω (n+1+d)) (f : FinitePath Ω (n+1+d) → Fin N → ℝ) :
    shapeEnergyAt C d T f=KernelTower.prefixEnergyAt (n+1+d) T d f := by
  induction d with
  | zero => exact childEnergy_singleton C hC T f
  | succ d ih => exact T.1.expect_congr (fun z => ih (T.2 z) (fun y => f (z,y)))

lemma prefixEnergyAt_heightCast {m n : ℕ} (h : n=m) (d : ℕ)
    (T : KernelTower Ω n) (f : FinitePath Ω n → Fin N → ℝ) :
    KernelTower.prefixEnergyAt m (kernelHeightCast h T) d (vectorHeightCast h f)=
      KernelTower.prefixEnergyAt n T d f := by
  cases h
  rfl

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

/-- The base topology in the SAME scheduled covariance family is exactly the
conditional singleton covariance controlled by joint_grid_selection. -/
lemma scheduledShapeEnergy_leaf (d : ℕ) (hd : d<L) (q : ReducedTopology.leaf.Vertex → ℕ)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) :
    scheduledShapeEnergy L d .leaf q T f=KernelTower.prefixEnergyAt L T d f := by
  rw [scheduledShapeEnergy_eq_realize (L-(d+1)) d .leaf q (by omega)]
  have hcard : Fintype.card (realize (L-(d+1)) (d+1) .leaf q).Leaf=1 := by
    rw [card_leaf,realize_leaves _ _ .leaf q trivial]
    rfl
  rw [shapeEnergyAt_singleton _ hcard,prefixEnergyAt_heightCast]

end DilutedSpinGlass.ReducedTopology
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
lemma physicalScheduledEnergy_leaf (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (Q : Option ReducedTopology.leaf.Vertex → Fin (L+1)) :
    physicalScheduledEnergy M θB hB N L u .leaf Q=
      physicalSingletonEnergy (gridExponents L) M θB hB N u (Q none).val := by
  unfold physicalScheduledEnergy physicalSingletonEnergy rootConditionalEnergy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => scheduledShapeEnergy_leaf _ (Q none).isLt _ _ _)


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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRegularSelection
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

noncomputable local instance fullRegularSelectionDecidableEq_r6b90f8_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

lemma FullShapeControl.matrix {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (k : ℕ) (hk : 0<k)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) :
    Tendsto (fun n => physicalTreeMatrixCovariance (gridExponents L) S a M C H
      (Ns n+1) (us n) T q) atTop (𝓝 0) := by
  let F := fun n => spatialProduct (fun _ : S.Leaf =>
    readVector (fun v x => readSpin (KernelTower.terminalState L x) v) (N := Ns n+1))
  have hF : ∀ n x, |F n x|≤1 := fun n x => spatialProduct_bound _
    (fun _ y i => readVector_bound _ y i) x
  have hs := h.shape S a F 1 (by norm_num) hF k (matrixSplitTest T q) true
  have he (n : ℕ) :
      physicalShapeCovariance (gridExponents L) S a M C H (Ns n+1) (us n)
        (matrixSplitTest T q) true (F n) =
        physicalTreeMatrixCovariance (gridExponents L) S a M C H (Ns n+1) (us n) T q := by
    rw [physicalShape_matrix hk (gridExponents L) (gridExponents_pos L)
      (gridExponents_mono L) (gridExponents_last L) S a M C H _ _ T q _
      (by norm_num : (0:ℝ)≤1) (hF n)]
    exact (physicalTreeMatrixCovariance_eq (gridExponents L) S a M C H _ _ T q).symm
  simpa only [he] using hs

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

lemma FullShapeControl.singleton_regular {M : Model p} {C H : ℝ}
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

lemma physicalShapeAverage_le_of_pointwise (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η b : ℝ) (hb : 0≤b)
    (h : ∀ Q, regularShapeDomain S (L+1) η Q → physicalScheduledEnergy M C H N L u S Q≤b) :
    physicalShapeAverage M C H N L u S η≤b :=
  DepthAverage.average_le_const _ _ hb h

lemma FullShapeControl.scheduled {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us) :
    ScheduledControl M C H L Ns us := by
  constructor
  · intro η hη t ht
    filter_upwards [h.singleton_regular hη ht] with n hn
    apply physicalShapeAverage_le_of_pointwise M C H (Ns n+1) L (us n) .leaf η _ (by positivity)
    intro Q hQ
    rw [physicalScheduledEnergy_leaf]
    exact hn (Q none) (by
      simp only [regularSingletonDepths,Finset.mem_filter,Finset.mem_univ,true_and]
      exact hQ.1.1 none)
  · intro α _ _ D S T a k hk q denom
    apply DepthAverage.tendsto_average_zero
    intro Q
    have hh := (h.matrix (S Q) (a Q) (k Q) (hk Q) (T Q) (q Q)).abs.div_const |denom Q|
    simpa only [abs_zero,zero_div] using hh

end DilutedSpinGlass.UniversalDictionary

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

lemma mixedVariance_le_one (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ)
    (hF : ∀ z w, |F z w|≤1) : mixedVariance μ Ω P F≤1 := by
  have he : ∀ z, (P z).expect (fun w => (F z w)^2)≤1 := by
    intro z
    exact ((P z).expect_mono (fun w => (sq_le_one_iff_abs_le_one _).mpr (hF z w))).trans_eq
      ((P z).expect_const 1)
  have h := integral_mono hFsq (integrable_const (1:ℝ)) he
  simp only [integral_const,probReal_univ,one_smul] at h
  unfold mixedVariance
  linarith [sq_nonneg (∫ z, (P z).expect (F z) ∂μ)]

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalOverlapConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance physicalOverlapConcentrationAverageDecidableEq_r6b90f8_1 (type : Type) :
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

end DilutedSpinGlass.DepthAverage

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

include hb hV in
lemma root_overlapVariance_le_one :
    overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V)≤1 := by
  apply FiniteLaw.mixedVariance_le_one
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2
  · intro z w
    rw [treeOverlap_eq_spatialProduct]
    exact spatialProduct_bound _ (fun _ y i => hV _ i) _

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

lemma physicalOverlapVariance_le_one (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (q : S.Vertex → Fin (L+1)) :
    physicalOverlapVariance M C H N L u S q≤1 := by
  unfold physicalOverlapVariance scheduledOverlapVariance
  exact root_overlapVariance_le_one _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

lemma physicalOverlapAverage_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalOverlapAverage M C H N L u S η :=
  DepthAverage.average_nonneg _ _ (physicalOverlapVariance_nonneg M C H N L u S)

lemma physicalOverlapAverage_le_one (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    physicalOverlapAverage M C H N L u S η≤1 :=
  DepthAverage.average_le_const _ _ (by norm_num) (fun q _ => physicalOverlapVariance_le_one M C H N L u S q)

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
lemma physicalOverlapLimsup_nonneg (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalOverlapLimsup M C H L Ns us S η :=
  unit_limsup_nonneg (fun n => physicalOverlapAverage_nonneg M C H (Ns n+1) L (us n) S η)
    (fun n => physicalOverlapAverage_le_one M C H (Ns n+1) L (us n) S η)

lemma physicalOverlapLimsup_antitone (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) :
    Antitone (physicalOverlapLimsup M C H L Ns us S) := by
  intro η ε hηε
  have hab (n : ℕ) : physicalOverlapAverage M C H (Ns n+1) L (us n) S ε≤
      physicalOverlapAverage M C H (Ns n+1) L (us n) S η := by
    apply DepthAverage.average_domain_bound
    · intro q hq
      refine ⟨⟨?_,?_⟩,hq.2⟩
      · intro v
        have hv := hq.1.1 v
        constructor <;> linarith
      · intro v w hvw
        exact hηε.trans_lt (hq.1.2 v w hvw)
    · intro q _; rfl
    · exact physicalOverlapVariance_nonneg M C H (Ns n+1) L (us n) S
  exact limsup_le_limsup (Eventually.of_forall hab)
    (IsCoboundedUnder.of_frequently_ge
      ((Eventually.of_forall (fun n => physicalOverlapAverage_nonneg M C H (Ns n+1) L (us n) S ε)).frequently))
    (isBoundedUnder_of_eventually_le
      (Eventually.of_forall (fun n => physicalOverlapAverage_le_one M C H (Ns n+1) L (us n) S η)))

lemma eventually_large_overlap_grid {η : ℝ} (hη : 0<η) :
    ∀ᶠ L : ℕ in atTop, 8<η*((L+1:ℕ):ℝ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (8/η)
  filter_upwards [eventually_ge_atTop n] with L hL
  have hc : (n:ℝ)≤((L+1:ℕ):ℝ) := by exact_mod_cast (show n≤L+1 by omega)
  have hd := (div_lt_iff₀ hη).mp (hn.trans_le hc)
  simpa only [mul_comm] using hd

/-- All root, auxiliary and thermal randomness are concentrated. Branch depths
alone are averaged; the topology and model are arbitrary and unchanged. -/
theorem physicalOverlapLimsup_tendsto (M : Model p) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L))
    (S : ReducedTopology) {η : ℝ} (hη : 0<η) :
    Tendsto (fun L => physicalOverlapLimsup M C H L (Ns L) (us L) S η) atTop (𝓝 0) := by
  let ε := min η 1
  have hε : 0<ε := lt_min hη (by norm_num)
  have hε1 : ε≤1 := min_le_right _ _
  have hs := (physicalShapeLimsup_tendsto M C H Ns us (fun L => (hcontrol L).scheduled)
    S (by positivity : 0<ε/8)).sqrt.div_const (ε/8)
  have hs' : Tendsto (fun L => Real.sqrt (physicalShapeLimsup M C H L (Ns L) (us L) S (ε/8))/(ε/8))
      atTop (𝓝 0) := by simpa using hs
  apply squeeze_zero' (Eventually.of_forall (fun L => physicalOverlapLimsup_nonneg M C H L (Ns L) (us L) S η)) _ hs'
  filter_upwards [eventually_large_overlap_grid hε] with L hL
  apply (physicalOverlapLimsup_antitone M C H L (Ns L) (us L) S (min_le_left _ _)).trans
  apply (le_div_iff₀ (by positivity : 0<ε/8)).mpr
  rw [mul_comm]
  exact physicalOverlapLimsup_bound (hcontrol L) S hε hε1 hL

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QTreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance qTreeLawDecidableEq_r6b90f8_1 (type : Type) :
    DecidableEq type := Classical.decEq type
theorem qExpect_const {n : ℕ} (m : Fin (n+1) → ℝ)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) (c : ℝ)
    (k : ℕ) (S : PrescribedTree n) : qExpect m (fun _ => c) k S = c := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect, ih]
    rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_neg_distrib, sum_gamma, hroot, hend]
    have hn : (leaves S:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (leaves_pos S))
    simp [hn]

theorem qExpect_mono {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) {F G : PrescribedTree n → ℝ}
    (hFG : ∀ S, F S ≤ G S) (k : ℕ) (S : PrescribedTree n) :
    qExpect m F k S ≤ qExpect m G k S := by
  induction k generalizing S with
  | zero => exact hFG S
  | succ k ih =>
    exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (ih (grow S v))
      (div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)))

lemma qExpect_nonneg {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (F : PrescribedTree n → ℝ)
    (hF : ∀ S, 0≤F S) (k : ℕ) (S : PrescribedTree n) : 0≤qExpect m F k S := by
  induction k generalizing S with
  | zero => exact hF S
  | succ k ih => exact Finset.sum_nonneg (fun v _ => mul_nonneg
      (div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)) (ih _))

lemma qExpect_sum {n : ℕ} (m : Fin (n+1) → ℝ) {ι : Type} (s : Finset ι)
    (F : ι → PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => ∑ i∈s, F i T) k S=∑ i∈s, qExpect m (F i) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,Finset.mul_sum]; exact Finset.sum_comm

lemma qExpect_mul_const {n : ℕ} (m : Fin (n+1) → ℝ)
    (F : PrescribedTree n → ℝ) (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T*c) k S=qExpect m F k S*c := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,Finset.sum_mul,mul_assoc]

lemma qExpect_grid_le_historyMass {L : ℕ} (hL : 0<L) (F : PrescribedTree L → ℝ)
    (hF : ∀ T, 0≤F T) (k : ℕ) (S : PrescribedTree L) :
    qExpect (grid L 0 L) F k S≤historyMass F k S 0 := by
  have hm : Monotone (grid L 0 L) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast (show 0+i.val≤0+j.val from Nat.add_le_add_left hij 0))
      (le_of_lt (Nat.cast_pos.mpr hL))
  have hp : ∀ j, 0≤grid L 0 L j := fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect,historyMass,CharP.cast_eq_zero,zero_mul,zero_add]
    apply Finset.sum_le_sum
    intro v _
    have hg : |gamma S (grid L 0 L) v| = -gamma S (grid L 0 L) v :=
      abs_of_nonpos (gamma_nonpos S _ hm hp v)
    rw [hg]
    have hcoef : -gamma S (grid L 0 L) v / S.leaves≤ -gamma S (grid L 0 L) v := by
      apply div_le_self (neg_nonneg.mpr (gamma_nonpos S _ hm hp v))
      exact_mod_cast leaves_pos S
    apply mul_le_mul hcoef (ih _) (qExpect_nonneg _ hm hp F hF k _) (neg_nonneg.mpr (gamma_nonpos S _ hm hp v))

lemma qExpect_grid_branching {L : ℕ} (hL : 0<L) (Q : Finset ℕ) (k b : ℕ)
    (S : PrescribedTree L) :
    qExpect (grid L 0 L) (fun T => if branchingCount S (·∈Q)+b≤branchingCount T (·∈Q)
      then 1 else 0) k S≤
    chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k b * (L:ℝ)⁻¹^b := by
  exact (qExpect_grid_le_historyMass hL _ (fun _ => by split_ifs <;> norm_num) k S).trans
    (charging_final_shape hL Q k b 0 S (Nat.zero_le _))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QTopologyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance qTopologyBoundDecidableEq_r6b90f8_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance qTopologyBoundDecidable_r6b90f8_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma chargeBound_mono {C D C' D' : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hCC : C ≤ C') (hDD : D ≤ D') (k b : ℕ) : chargeBound C D k b ≤ chargeBound C' D' k b := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    cases b with
    | zero => exact mul_le_mul hCC (ih 0) (chargeBound_nonneg hC hD _ _) (hC.trans hCC)
    | succ b =>
      exact add_le_add
        (mul_le_mul hCC (ih _) (chargeBound_nonneg hC hD _ _) (hC.trans hCC))
        (mul_le_mul hDD (ih _) (chargeBound_nonneg hC hD _ _) (hD.trans hDD))

lemma shapeCharge_nonneg (k : ℕ) (S : ReducedTopology) : 0 ≤ shapeCharge k S :=
  chargeBound_nonneg (by positivity) (by positivity) _ _

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularBadMass
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance regularBadMassDecidableEq_r6b90f8_1 (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.regularBadMassDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma uniform_indicator_eq (P : Fin L → Prop) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x => if P x then (1:ℝ) else 0)=
      ((Finset.univ.filter P).card:ℝ)/(L:ℝ) := by
  unfold FiniteLaw.expect FiniteLaw.uniform
  simp only [Fintype.card_fin]
  rw [← Finset.mul_sum,← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,div_eq_mul_inv,mul_comm]

lemma uniform_interval_le (a b : ℕ) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x => if a ≤ x.val ∧ x.val ≤ b then (1:ℝ) else 0)  ≤ 
      ((b+1-a:ℕ):ℝ)/(L:ℝ) := by
  have he := uniform_indicator_eq (L := L) (fun x : Fin L => a ≤ x.val ∧ x.val ≤ b)
  have he' : (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x => if a ≤ x.val ∧ x.val ≤ b then (1:ℝ) else 0) =
      ((Finset.univ.filter (fun x : Fin L => a ≤ x.val ∧ x.val ≤ b)).card:ℝ)/(L:ℝ) := by
    convert he using 1
    · congr 1; funext x; split_ifs <;> rfl
    · congr 3; ext x; simp
  rw [he']
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun x : Fin L => a ≤ x.val ∧ x.val ≤ b))
    (t := Finset.Icc a b) Fin.val
    (by intro x hx; exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hx).2)
    (by intro x hx y hy hxy; exact Fin.ext hxy)
  simpa only [Nat.card_Icc] using h

lemma uniform_boundary_le (r : ℕ) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x => if x.val ≤ r ∨ L ≤ x.val+r then (1:ℝ) else 0)  ≤ 
      (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  have hmono := (FiniteLaw.uniform : FiniteLaw (Fin L)).expect_mono (fun x =>
    (show (if x.val ≤ r ∨ L ≤ x.val+r then (1:ℝ) else 0)  ≤ 
       (if 0 ≤ x.val ∧ x.val ≤ r then 1 else 0)+(if L-r ≤ x.val ∧ x.val ≤ L-1 then 1 else 0) by
      have hxr : x.val ≤ L-1 := by have := x.isLt; omega
      have hriff : L ≤ x.val+r ↔ L-r ≤ x.val := by omega
      simp only [hriff,Nat.zero_le,true_and,hxr,and_true]
      split_ifs <;> norm_num at *
      omega))
  rw [FiniteLaw.expect_add] at hmono
  apply hmono.trans
  apply (add_le_add (uniform_interval_le 0 r) (uniform_interval_le (L-r) (L-1))).trans
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h : (r+1-0)+(L-1+1-(L-r)) ≤ 2*(r+1) := by omega
  exact_mod_cast h

lemma uniform_near_le (r : ℕ) (y : Fin L) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x =>
      if x.val ≤ y.val+r ∧ y.val ≤ x.val+r then (1:ℝ) else 0)  ≤  (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  have he : (fun x : Fin L => if x.val ≤ y.val+r ∧ y.val ≤ x.val+r then (1:ℝ) else 0)=
      (fun x => if y.val-r ≤ x.val ∧ x.val ≤ y.val+r then 1 else 0) := by
    funext x
    have h : (x.val ≤ y.val+r ∧ y.val ≤ x.val+r) ↔ (y.val-r ≤ x.val ∧ x.val ≤ y.val+r) := by omega
    simp only [h]
  rw [he]
  apply (uniform_interval_le (y.val-r) (y.val+r)).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (show y.val+r+1-(y.val-r) ≤ 2*(r+1) by omega)

lemma average_boundary_le (r : ℕ) (i : α) :
    average (fun q : α → Fin L => (q i).val ≤ r ∨ L ≤ (q i).val+r) (fun _ => 1)  ≤ 
      (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  unfold average depthLaw
  have he := FiniteLaw.expect_pi_marginal (fun _ : α => (FiniteLaw.uniform : FiniteLaw (Fin L))) i
    (fun x => if x.val ≤ r ∨ L ≤ x.val+r then (1:ℝ) else 0)
  convert he.le.trans (uniform_boundary_le r) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1; funext depth; split_ifs <;> rfl

lemma average_near_le (r : ℕ) (i j : α) (hij : i≠j) :
    average (fun q : α → Fin L => (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r) (fun _ => 1)  ≤ 
      (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  rw [average_split_comm i]
  apply (FiniteLaw.expect_mono _ (fun rest => ?_)).trans_eq (FiniteLaw.expect_const _ _)
  have hj : j≠i := Ne.symm hij
  simp only [insertCoordinate_self]
  have hrest (t : Fin L) : insertCoordinate i t rest j=rest ⟨j,hj⟩ := insertCoordinate_other i t rest ⟨j,hj⟩
  simp only [hrest]
  exact uniform_near_le r (rest ⟨j,hj⟩)

omit [Fintype α] [DecidableEq α] in
lemma regular_of_discrete {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ) ≤ r) (q : α → Fin L)
    (hb : ∀ i, ¬((q i).val ≤ r ∨ L ≤ (q i).val+r))
    (hc : ∀ i j, i≠j → ¬((q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r)) : Regular η q := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  constructor
  · intro i
    obtain ⟨hi,hj⟩ := not_or.mp (hb i)
    have hi' : (r:ℝ)<(q i).val := by exact_mod_cast Nat.lt_of_not_ge hi
    have hj' : ((q i).val:ℝ)+r<L := by exact_mod_cast Nat.lt_of_not_ge hj
    constructor
    · exact (lt_div_iff₀ hL).mpr (hηr.trans_lt hi')
    · apply (div_lt_iff₀ hL).mpr
      nlinarith
  · intro i j hij
    have hh := hc i j hij
    have hd : (r:ℝ) < |((q i).val:ℝ)-(q j).val| := by
      by_cases h : (q i).val ≤ (q j).val+r
      · have h' : (q i).val+r<(q j).val := by omega
        have hr : ((q i).val:ℝ)+r<(q j).val := by exact_mod_cast h'
        rw [abs_of_neg (by linarith : ((q i).val:ℝ)-(q j).val<0)]
        linarith
      · have hr : ((q j).val:ℝ)+r<(q i).val := by exact_mod_cast Nat.lt_of_not_ge h
        rw [abs_of_pos (by linarith : 0<((q i).val:ℝ)-(q j).val)]
        linarith
    unfold normalized
    rw [← sub_div,abs_div,abs_of_pos hL]
    exact (lt_div_iff₀ hL).mpr (hηr.trans_lt hd)

lemma nonregular_pointwise {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ) ≤ r) (q : α → Fin L) :
    (if ¬Regular η q then (1:ℝ) else 0)  ≤ 
      (∑ i, if (q i).val ≤ r ∨ L ≤ (q i).val+r then 1 else 0)+
      ∑ i, ∑ j, if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then 1 else 0 := by
  have hn (P : Prop) : (0:ℝ) ≤ if P then 1 else 0 := by split_ifs <;> norm_num
  have hbn : 0 ≤ ∑ i, if (q i).val ≤ r ∨ L ≤ (q i).val+r then (1:ℝ) else 0 := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hcn : 0 ≤ ∑ i, ∑ j, if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  by_cases hb : ∃ i, (q i).val ≤ r ∨ L ≤ (q i).val+r
  · obtain ⟨i,hi⟩ := hb
    have hs : 1 ≤ ∑ j : α, if (q j).val ≤ r ∨ L ≤ (q j).val+r then (1:ℝ) else 0 := by
      calc
        1 = (if (q i).val ≤ r ∨ L ≤ (q i).val+r then (1:ℝ) else 0) := by rw [ite_eq_left hi]
        _ ≤ _ := Finset.single_le_sum (f := fun j : α => if (q j).val ≤ r ∨ L ≤ (q j).val+r then (1:ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    split_ifs <;> linarith
  · by_cases hc : ∃ i j, i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r
    · obtain ⟨i,j,hij⟩ := hc
      have hs : 1 ≤ ∑ j' : α, if i≠j' ∧ (q i).val ≤ (q j').val+r ∧ (q j').val ≤ (q i).val+r then (1:ℝ) else 0 := by
        calc
          1 = (if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0) := by rw [ite_eq_left hij]
          _ ≤ _ := Finset.single_le_sum (f := fun j' : α => if i≠j' ∧ (q i).val ≤ (q j').val+r ∧ (q j').val ≤ (q i).val+r then (1:ℝ) else 0) (fun j' _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
      have ht : (∑ j' : α, if i≠j' ∧ (q i).val ≤ (q j').val+r ∧ (q j').val ≤ (q i).val+r then (1:ℝ) else 0) ≤
          ∑ i' : α, ∑ j' : α, if i'≠j' ∧ (q i').val ≤ (q j').val+r ∧ (q j').val ≤ (q i').val+r then (1:ℝ) else 0 :=
        Finset.single_le_sum (f := fun i' : α => ∑ j' : α, if i'≠j' ∧ (q i').val ≤ (q j').val+r ∧ (q j').val ≤ (q i').val+r then (1:ℝ) else 0) (fun i' _ => Finset.sum_nonneg (fun j' _ => by split_ifs <;> norm_num)) (Finset.mem_univ i)
      split_ifs <;> linarith
    · have hr := regular_of_discrete hηr q (by simpa only [not_exists] using hb)
        (by simpa only [not_exists,not_and] using hc)
      rw [ite_eq_right (not_not.mpr hr)]
      exact add_nonneg hbn hcn

lemma nonregular_average_bound {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ) ≤ r) :
    average (fun q : α → Fin L => ¬Regular η q) (fun _ => 1)  ≤ 
      ((Fintype.card α:ℝ)+(Fintype.card α:ℝ)^2)*(2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  have hm := (depthLaw α L).expect_mono (nonregular_pointwise hηr)
  rw [FiniteLaw.expect_add,FiniteLaw.expect_fintype_sum] at hm
  simp_rw [FiniteLaw.expect_fintype_sum] at hm
  apply le_trans (b := (∑ i : α, (depthLaw α L).expect (fun q => if (q i).val ≤ r ∨ L ≤ (q i).val+r then (1:ℝ) else 0)) +
    ∑ i : α, ∑ j : α, (depthLaw α L).expect (fun q => if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0))
  · convert hm using 1
    all_goals try with_reducible_and_instances rfl
    unfold average; congr 1; funext depth; split_ifs <;> rfl
  have hc (i j : α) : (depthLaw α L).expect (fun q =>
      if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0)  ≤  (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
    by_cases hij : i=j
    · subst j
      simp only [ne_eq,not_true_eq_false,false_and,ite_false,FiniteLaw.expect_const]
      positivity
    · have hh := average_near_le (L := L) r i j hij
      unfold average at hh
      convert hh using 1
      · congr 1
        funext q
        dsimp only
        by_cases hq : (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r
        · simp only [ite_eq_left hq,ite_eq_left (And.intro hij hq)]
        · simp only [ite_eq_right hq,ite_eq_right (not_and_of_not_right _ hq)]
  have hb := Finset.sum_le_sum (fun (i : α) (_ : i∈Finset.univ) => average_boundary_le (L := L) r i)
  have ht := Finset.sum_le_sum (fun (i : α) (_ : i∈Finset.univ) => Finset.sum_le_sum (fun (j : α) (_ : j∈Finset.univ) => hc i j))
  have hs := add_le_add hb ht
  have hs' : (∑ i : α, average (fun q : α → Fin L => (q i).val ≤ r ∨ L ≤ (q i).val+r) (fun _ => 1)) +
      (∑ i : α, ∑ j : α, (depthLaw α L).expect (fun q => if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0)) ≤
      ((Fintype.card α:ℝ)+(Fintype.card α:ℝ)^2)*(2*(r+1:ℕ):ℝ)/(L:ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    apply hs.trans_eq
    push_cast
    ring
  apply le_trans (b := (∑ i : α, average (fun q : α → Fin L => (q i).val ≤ r ∨ L ≤ (q i).val+r) (fun _ => 1)) +
      (∑ i : α, ∑ j : α, (depthLaw α L).expect (fun q => if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0))) _ hs'
  apply le_of_eq
  apply congrArg (fun x => x+_)
  apply Finset.sum_congr rfl
  intro i _
  unfold average
  congr 1; funext q; split_ifs <;> rfl

end DilutedSpinGlass.DepthAverage

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance finiteEncodingAverageDecidableEq_r6b90f8_1 (type : Type) :
    DecidableEq type := Classical.decEq type
attribute [local instance] OAI.DilutedSpinGlass.DepthAverage.finiteEncodingAverageDecidable
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_split_regular_le (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    (h0 : ∀ q, 0 ≤ F q) (h1 : ∀ q, F q ≤ 1) (η : ℝ) :
    average D F ≤ average (fun q => Regular η q ∧ D q) F+
      average (fun q : α → Fin L => ¬Regular η q) (fun _ => 1) := by
  unfold average
  rw [← FiniteLaw.expect_add]
  apply FiniteLaw.expect_mono
  intro q
  dsimp only
  by_cases hd : D q <;> by_cases hr : Regular η q <;>
    simp only [hd,hr,true_and,false_and,not_true_eq_false,not_false_eq_true,ite_true,ite_false] <;>
    first
    | simpa only [zero_add] using (h0 q).trans (h1 q)
    | linarith [h1 q]

lemma weighted_sum_eq_average (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) (c : ℝ) :
    (∑ q : α → Fin L, if D q then c*(L:ℝ)⁻¹^(Fintype.card α)*F q else 0)=c*average D F := by
  rw [average_eq,Finset.sum_filter,div_eq_mul_inv,← inv_pow]
  rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> ring

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage
open scoped BigOperators

noncomputable local instance finiteEncodingTreeDecidableEq_r6b90f8_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance finiteEncodingTreeDecidable_r6b90f8_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma shapeBadConstant_nonneg (S : ReducedTopology) : 0 ≤ shapeBadConstant S := by
  unfold shapeBadConstant
  positivity

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QSubtreePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubtreePotentialDecidableEq
attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubtreePotentialPropDecidable
lemma qEmbed_realize_le {L : ℕ} (hL : 0<L) (k : ℕ) (S : ReducedTopology)
    (q : S.Vertex → Fin L) (hq : S.Admissible (fun v => q v) 0 L) :
    qExpect (grid L 0 L) (fun T => if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then 1 else 0)
      k (single L) ≤ shapeCharge k S * (L:ℝ)⁻¹^(Fintype.card S.Vertex) := by
  let Q : Finset ℕ := Finset.univ.image (fun v => (q v).val)
  have hQ : Q.card ≤ Fintype.card S.Vertex := (Finset.card_image_le).trans_eq (Finset.card_univ)
  have hb : branchingCount (S.realize L 0 (fun v => q v)) (·∈Q)=Fintype.card S.Vertex := by
    have h := S.realize_branchingCount L 0 (fun v => q v) (by simpa using hq) (·∈Q)
    have hm (v : S.Vertex) : (q v).val∈Q := Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
    simpa only [Nat.zero_add,hm,ite_true,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using h
  apply le_trans (b := qExpect (grid L 0 L) (fun T =>
    if branchingCount (single L) (·∈Q)+Fintype.card S.Vertex ≤ branchingCount T (·∈Q) then 1 else 0) k (single L))
  · apply qExpect_mono _ (grid_strictMono hL).monotone grid_nonneg
    intro T
    by_cases he : Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T)
    · obtain ⟨f⟩ := he
      have ht := f.branchingCount_le (·∈Q)
      rw [hb] at ht
      have hf : Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) := ⟨f⟩
      simp only [ite_eq_left hf,branchingCount_single,zero_add,ite_eq_left ht,le_refl]
    · rw [ite_eq_right he]
      split_ifs <;> norm_num
  apply (qExpect_grid_branching hL Q k (Fintype.card S.Vertex) (single L)).trans
  rw [leaves_single]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply chargeBound_mono (by positivity) (by positivity) le_rfl
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hQ) (Nat.cast_nonneg _)

lemma subtreePotential_nonneg {L K : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T) (T) :
    0≤ subtreePotential K F T := by
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> first | exact hF _ | rfl

lemma qExpect_subtree_depth_bound {L : ℕ} [NeZero L] (K k : ℕ)
    (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T) :
    qExpect (grid L 0 L) (subtreePotential K F) k (single L) ≤
      ∑ S∈boundedTopologies K, shapeCharge k S *
        average (fun q : S.Vertex → Fin L => S.Admissible (fun v => q v) 0 L)
          (fun q => F (S.realize L 0 (fun v => q v))) := by
  unfold subtreePotential
  rw [qExpect_sum]
  apply Finset.sum_le_sum
  intro S _
  rw [qExpect_sum,← weighted_sum_eq_average]
  apply Finset.sum_le_sum
  intro q _
  by_cases hq : S.Admissible (fun v => q v) 0 L
  · simp only [hq,ite_true]
    have he : (fun T => if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then F (S.realize L 0 (fun v => q v)) else 0)=
        (fun T => (if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then 1 else 0)*F (S.realize L 0 (fun v => q v))) := by
      funext T; split_ifs <;> simp
    rw [he,qExpect_mul_const]
    exact mul_le_mul_of_nonneg_right (qEmbed_realize_le (NeZero.pos L) k S q hq) (hF _)
  · have hroot : grid L 0 L 0=0 := by simp [grid]
    simp only [hq,ite_false,qExpect_const _ hroot (grid_last (NeZero.pos L)),le_refl]

lemma qExpect_subtree_regular_bound {L : ℕ} [NeZero L] (K k : ℕ)
    (F : PrescribedTree L → ℝ) (h0 : ∀ T, 0≤F T) (h1 : ∀ T, F T≤1)
    {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ) ≤ r) :
    qExpect (grid L 0 L) (subtreePotential K F) k (single L) ≤
      ∑ S∈boundedTopologies K, shapeCharge k S *
        (average (regularOverlapDomain S L η) (fun q => F (S.realize L 0 (fun v => q v)))+
          shapeBadConstant S*(2*(r+1:ℕ):ℝ)/(L:ℝ)) := by
  apply (qExpect_subtree_depth_bound K k F h0).trans
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (shapeCharge_nonneg k S)
  apply (average_split_regular_le _ _ (fun q => h0 _) (fun q => h1 _) η).trans
  exact add_le_add le_rfl (nonregular_average_bound hηr)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TopologyDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage Filter Set
open scoped BigOperators Topology

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.topologyDecayDecidableEq
noncomputable local instance topologyDecayDecidable_r6b90f8_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma ceil_boundary_bound {L : ℕ} (hL : 0<L) {η : ℝ} (hη : 0≤η) :
    (2*(⌈η*(L:ℝ)⌉₊+1:ℕ):ℝ)/(L:ℝ) ≤ 2*η+4/(L:ℝ) := by
  have hh := (Nat.ceil_lt_add_one (mul_nonneg hη (Nat.cast_nonneg L))).le
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  apply (div_le_iff₀ hLr).mpr
  push_cast
  rw [add_mul,div_mul_cancel₀ _ hLr.ne']
  nlinarith

lemma qExpect_subtree_eta_bound {L : ℕ} [NeZero L] (K k : ℕ)
    (F : PrescribedTree L → ℝ) (h0 : ∀ T, 0≤F T) (h1 : ∀ T, F T≤1)
    {η : ℝ} (hη : 0≤η) :
    qExpect (grid L 0 L) (subtreePotential K F) k (single L) ≤
      ∑ S∈boundedTopologies K, shapeCharge k S *
        (average (regularOverlapDomain S L η) (fun q => F (S.realize L 0 (fun v => q v)))+
          shapeBadConstant S*(2*η+4/(L:ℝ))) := by
  apply (qExpect_subtree_regular_bound K k F h0 h1 (Nat.le_ceil (η*(L:ℝ)))).trans
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (shapeCharge_nonneg k S)
  apply add_le_add le_rfl
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (ceil_boundary_bound (NeZero.pos L) hη) (shapeBadConstant_nonneg S)

 
theorem qSubtree_limsup_tendsto (K k : ℕ)
    (F : (L : ℕ) → ℕ → PrescribedTree (L+1) → ℝ)
    (h0 : ∀ L n T, 0≤F L n T) (h1 : ∀ L n T, F L n T≤1)
    (hdecay : ∀ S : ReducedTopology, ∀ η : ℝ, 0<η →
      Tendsto (fun L => limsup (fun n => average (regularOverlapDomain S (L+1) η)
        (fun q => F L n (S.realize (L+1) 0 (fun v => q v)))) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (subtreePotential K (F L n)) k (single (L+1))) atTop) atTop (𝓝 0) := by
  let a (L n : ℕ) := qExpect (grid (L+1) 0 (L+1)) (subtreePotential K (F L n)) k (single (L+1))
  have ha (L n : ℕ) : 0≤a L n := qExpect_nonneg _ (grid_strictMono (by omega)).monotone grid_nonneg
    _ (subtreePotential_nonneg _ (h0 L n)) _ _
  have hb (L : ℕ) (η : ℝ) (hη : 0≤η) : limsup (a L) atTop≤
      ∑ S∈boundedTopologies K, shapeCharge k S *
        (limsup (fun n => average (regularOverlapDomain S (L+1) η)
          (fun q => F L n (S.realize (L+1) 0 (fun v => q v)))) atTop +
          shapeBadConstant S*(2*η+4/(L+1:ℕ))) := by
    apply limsup_finite_linear_bound _ _ _ _ _ (fun S _ => shapeCharge_nonneg k S) (ha L)
      (fun S _ n => average_le_const _ _ (by norm_num) (fun q _ => h1 L n _))
    intro n
    exact qExpect_subtree_eta_bound K k (F L n) (h0 L n) (h1 L n) hη
  have hl (L : ℕ) : 0≤limsup (a L) atTop := by
    have hcap (n : ℕ) : a L n≤∑ S∈boundedTopologies K, shapeCharge k S*(1+shapeBadConstant S*(2+4/(L+1:ℕ))) := by
      apply (qExpect_subtree_eta_bound K k (F L n) (h0 L n) (h1 L n) (by norm_num : (0:ℝ)≤1)).trans
      apply Finset.sum_le_sum
      intro S _
      apply mul_le_mul_of_nonneg_left _ (shapeCharge_nonneg k S)
      apply add_le_add
      · exact average_le_const _ _ (by norm_num) (fun q _ => h1 L n _)
      · norm_num
    apply le_limsup_of_le (show IsBoundedUnder (·≤·) atTop (a L) from
      isBoundedUnder_of_eventually_le (Eventually.of_forall hcap))
    intro b hb
    obtain ⟨n,hn⟩ := hb.exists
    exact (ha L n).trans hn
  let C := ∑ S∈boundedTopologies K, shapeCharge k S*shapeBadConstant S*2
  have hC : 0≤C := Finset.sum_nonneg (fun S _ => by
    have := shapeCharge_nonneg k S; have := shapeBadConstant_nonneg S; positivity)
  apply squeeze_triangle_grid_zero _ C hl hC
    (fun η L => ∑ S∈boundedTopologies K, shapeCharge k S *
      (limsup (fun n => average (regularOverlapDomain S (L+1) η)
        (fun q => F L n (S.realize (L+1) 0 (fun v => q v)))) atTop +
        shapeBadConstant S*(2*η+4/(L+1:ℕ)))) _ (fun η hη L => hb L η hη.le)
  intro η hη
  have ht : Tendsto (fun L : ℕ => (4:ℝ)/(L+1:ℕ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hh := tendsto_finsetSum (boundedTopologies K) (fun S _ =>
    ((hdecay S η hη).add (((tendsto_const_nhds (x := 2*η)).add ht).const_mul (shapeBadConstant S))).const_mul (shapeCharge k S))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_add,add_zero,C,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  ring

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalSubtreeConcentration
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

noncomputable local instance physicalSubtreeConcentrationDecidableEq_r6b90f8_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma physicalTreeVariance_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    0≤physicalTreeVariance M C H N L u T := by
  unfold physicalTreeVariance
  exact root_overlapVariance_nonneg _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

lemma physicalTreeVariance_le_one (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    physicalTreeVariance M C H N L u T≤1 := by
  unfold physicalTreeVariance
  exact root_overlapVariance_le_one _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

/-- The actual physical subsequence, not a newly assumed concentration law. -/
theorem physicalSubtree_limsup_tendsto_oai (M : Model p) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (K k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (subtreePotential K (physicalTreeVariance M C H (Ns L n+1) L (us L n)))
      k (single (L+1))) atTop) atTop (𝓝 0) := by
  apply qSubtree_limsup_tendsto K k
    (fun L n => physicalTreeVariance M C H (Ns L n+1) L (us L n))
    (fun L n => physicalTreeVariance_nonneg _ _ _ _ _ _)
    (fun L n => physicalTreeVariance_le_one _ _ _ _ _ _)
  intro S η hη
  exact physicalOverlapLimsup_tendsto M C H Ns us hcontrol S hη

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto_oai := @OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto_oai
