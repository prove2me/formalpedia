-- Prove2me | solution 1 for OAI.DilutedSpinGlass.ConcreteReservoir.physical_coefficients_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T07:59:15.252868+00:00
-- url     : https://prove2.me/submissions/fc10eb54-5b9d-4fa8-9bf2-7af4bea94f95

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

variable {n : ℕ}

/-- Exact insertion identity for a single finite backward step. -/
theorem logMean_insertion {m : ℝ} (f a : Ω → ℝ) :
    P.logMean m (fun x => f x + a x) - P.logMean m f =
      (P.tilt m f).logMean m a := by
  have hmom : (P.tilt m f).expMoment m a =
      P.expMoment m (fun x => f x + a x) / P.expMoment m f := by
    rw [expMoment, tilt_expect]
    congr 1
    exact P.expect_congr (fun x => by rw [mul_add, Real.exp_add])
  rw [logMean, logMean, logMean, hmom,
    Real.log_div (ne_of_gt (P.expMoment_pos _ _)) (ne_of_gt (P.expMoment_pos _ _)),
    sub_div]

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

/-- Exact composition of two one-step insertions, with no support assumption. -/
theorem tilt_insertion (m : ℝ) (f a : Ω → ℝ) :
    (P.tilt m f).tilt m a = P.tilt m (fun x => f x + a x) := by
  apply weights_ext
  intro x
  have he : (P.tilt m f).expMoment m a =
      P.expMoment m (fun x => f x + a x) / P.expMoment m f := by
    rw [expMoment, tilt_expect]
    congr 1
    exact P.expect_congr (fun x => by rw [mul_add, Real.exp_add])
  change (P.weight x * Real.exp (m * f x) / P.expMoment m f) * Real.exp (m * a x) /
    (P.tilt m f).expMoment m a = _
  rw [he]
  simp only [tilt, mul_add, Real.exp_add]
  field_simp [ne_of_gt (P.expMoment_pos m f)]

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

 
theorem insertion (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (f a : FinitePath Ω n → ℝ) :
    backwardLog n T m (fun x => f x + a x) - backwardLog n T m f =
      backwardLog n (tilt n T m f) m a := by
  induction n with
  | zero => simp only [backwardLog]; ring
  | succ n ih =>
    let F := fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y))
    let A := fun x => backwardLog n
      (tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
      (fun j => m j.succ) (fun y => a (x,y))
    have hc : (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
        (fun y => f (x,y) + a (x,y))) = (fun x => F x + A x) := by
      funext x
      have hi := ih (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))
      change _ - F x = A x at hi
      linarith
    change T.1.logMean (m 0) _ - T.1.logMean (m 0) F =
      (T.1.tilt (m 0) F).logMean (m 0) A
    rw [hc]
    exact T.1.logMean_insertion F A



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

/-- Updated kernels after an insertion agree with the successive tilting of
all the old tilted kernels. This is tree:updated-kernel at every depth. -/
theorem tilt_insertion (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (f a : FinitePath Ω n → ℝ) :
    tilt n (tilt n T m f) m a = tilt n T m (fun x => f x + a x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change (T.1.tilt (m 0) _).tilt (m 0) _ = T.1.tilt (m 0) _
      rw [FiniteLaw.tilt_insertion]
      congr 1
      funext x
      have h := insertion n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))
      change _ + backwardLog n (tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
        (fun j => m j.succ) (fun y => a (x,y)) = _
      linarith
    · funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))

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

/-- For positive affine insertions, the logarithmic score is D/A, with the
actual (not a formal or assumed) analytic derivative. -/
theorem hasDerivAt_log_affine {D u : ℝ} (hu : 1 + u*D ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (1+t*D)) (D/(1+u*D)) u := by
  simpa using (((hasDerivAt_id u).mul_const D).const_add 1).log hu

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

variable {Ω : Type} [Fintype Ω]

/-- The operational one-step differential recursion underlying *every* order
of the logarithmic and old-replica series. -/
theorem hasDerivAt_fullyProtected {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (G : Sample Ω S → ℝ) (u : ℝ)
    (hu : ∀ y, 0 < 1+u*D y) :
    HasDerivAt (fullyProtected S T m D G)
      (∑ v : Internal S, gamma S m v *
        fullyProtected (grow S v) T m D (fun x => G (oldSample S v x) * D (newPath S v x)) u) u := by
  classical
  let f (t : ℝ) (y : FinitePath Ω n) := Real.log (1+t*D y)
  let A (y : FinitePath Ω n) := 1+u*D y
  let DL (y : FinitePath Ω n) := D y / A y
  let T' := KernelTower.tilt n T (fun j => m j.succ) (f u)
  have hf (y : FinitePath Ω n) : HasDerivAt (fun t => f t y) (DL y) u := by
    have hh := ((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).mul_const (D y))).log
      (ne_of_gt (hu y))
    simpa [f, DL] using hh
  have hd := protected_leaf_extension_rule S T m hm hroot hend Finset.univ G hf
  have hfun : (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G x * Real.exp (-protectedLog S Finset.univ (f t) x))) =
      fullyProtected S T m D G := by
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
    (D (newPath S v x) / A (newPath S v x)) =
    (G (oldSample S v x) * D (newPath S v x)) * Real.exp (-leafSum (grow S v) (f u) x)
  rw [leafSum_grow, neg_add, Real.exp_add]
  change _ = _ * (Real.exp (-leafSum S (f u) (oldSample S v x)) *
    Real.exp (-Real.log (A (newPath S v x))))
  rw [Real.exp_neg (Real.log (A (newPath S v x))),
    Real.exp_log (show 0 < A (newPath S v x) from hu _)]
  ring

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

theorem poisson_integrable_linear (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*n) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

theorem poisson_integrable_count_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hnext : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have hs := (hasSum_integral_poissonMeasure hnext).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : Summable (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)^2) := by
    simp_rw [pow_two, ← mul_assoc, poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs.summable
  have ht' := Summable.comp_nat_add (f := fun n => poissonWeight r n * (n : ℝ)^2) (k := 1) ht
  simpa only [Real.norm_eq_abs, abs_sq, poissonWeight] using ht'

@[simp] theorem poisson_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2 + r := by
  have hi : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have h := poisson_add_one r (fun n => (n : ℝ)) hi
  simp only [← pow_two, Nat.cast_add, Nat.cast_one] at h
  rw [integral_add (poisson_integrable_count r) (integrable_const 1), poisson_mean,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductTowers
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

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Conditional power means commute with literal relabeling of every hidden
mark variable. This is needed for the physical Palm exchangeability. -/
theorem backwardLog_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n (transport e n T) m f =
      backwardLog n T m (f ∘ pathEquiv e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, transport]
    have he : (fun a : Λ => backwardLog n (transport e n (T.2 (e.symm a)))
        (fun j => m j.succ) (fun y => f (a,y))) =
      (fun a : Λ => backwardLog n (T.2 (e.symm a))
        (fun j => m j.succ) ((fun y => f (a,y)) ∘ pathEquiv e n)) :=
      funext (fun a => ih (T.2 (e.symm a)) (fun j => m j.succ) (fun y => f (a,y)))
    rw [he, FiniteLaw.logMean_transport]
    congr 1
    funext a
    simp only [Function.comp_def, Equiv.symm_apply_apply, pathEquiv_cons]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

theorem eq_of_weights {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

theorem tilt_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω) (m : ℝ) (f : Λ → ℝ) :
    (P.transport e).tilt m f = (P.tilt m (f ∘ e)).transport e := by
  apply eq_of_weights
  intro y
  change P.weight (e.symm y) * Real.exp (m * f y) /
    (P.transport e).expMoment m f =
      P.weight (e.symm y) * Real.exp (m * f (e (e.symm y))) / P.expMoment m (f ∘ e)
  rw [expMoment_transport, Equiv.apply_symm_apply]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem tilt_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    tilt n (transport e n T) m f =
      transport e n (tilt n T m (f ∘ pathEquiv e n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · simp only [tilt, transport, FiniteLaw.tilt_transport]
      congr 2
      funext a
      simp only [Function.comp_def, Equiv.symm_apply_apply, backwardLog_transport,
        pathEquiv_cons]
    · funext a
      simp only [tilt, transport, ih, Function.comp_def, pathEquiv_cons, Equiv.apply_symm_apply]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem sampleWeight_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (x : Sample Ω S) :
    (sampleLaw S (KernelTower.transport e n T)).weight (sampleEquiv e S x) =
      (sampleLaw S T).weight x := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    rcases T with ⟨P, T⟩
    change (∏ i, P.weight (e.symm (e (x i).1)) *
      (sampleLaw (C i) (KernelTower.transport e n (T (e.symm (e (x i).1))))).weight
        (sampleEquiv e (C i) (x i).2)) =
      ∏ i, P.weight (x i).1 * (sampleLaw (C i) (T (x i).1)).weight (x i).2
    simp only [Equiv.symm_apply_apply]
    apply Finset.prod_congr rfl
    intro i _
    rw [ih]

theorem sampleExpect_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (f : Sample Λ S → ℝ) :
    (sampleLaw S (KernelTower.transport e n T)).expect f =
      (sampleLaw S T).expect (f ∘ sampleEquiv e S) := by
  unfold FiniteLaw.expect
  apply (Fintype.sum_equiv (sampleEquiv e S) _ _ ?_).symm
  intro x
  simp only [sampleWeight_transport, Function.comp_apply]

theorem tiltedSampleExpect_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ)
    (g : Sample Λ S → ℝ) :
    (sampleLaw S (KernelTower.tilt n (KernelTower.transport e n T) m f)).expect g =
      (sampleLaw S (KernelTower.tilt n T m (f ∘ KernelTower.pathEquiv e n))).expect
        (g ∘ sampleEquiv e S) := by
  rw [KernelTower.tilt_transport, sampleExpect_transport]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type}

/-- A leaf keeps its label under relabeling, even when two sampled paths agree. -/
theorem pathAt_sampleEquiv (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (x : Sample Ω S) :
    pathAt S a (sampleEquiv e S x) = KernelTower.pathEquiv e n (pathAt S a x) := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    change (e (x a.1).1, pathAt (C a.1) a.2 (sampleEquiv e (C a.1) (x a.1).2)) =
      (e (x a.1).1, KernelTower.pathEquiv e n (pathAt (C a.1) a.2 (x a.1).2))
    rw [ih]

end DilutedSpinGlass.PrescribedTree

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
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem perturb_factor_lower {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    (1:ℝ)/2 ≤ 1+t*D q y+u*E q y := by
  have ht' := mul_le_mul_of_nonneg_left (hD q y) (abs_nonneg t)
  have hu' := mul_le_mul_of_nonneg_left (hE q y) (abs_nonneg u)
  rw [← abs_mul, mul_one] at ht' hu'
  linarith [(abs_le.mp (ht'.trans ht)).1, (abs_le.mp (hu'.trans hu)).1]

omit [Fintype Ω] in
theorem perturb_fraction_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    |E q y / (1+t*D q y+u*E q y)| ≤ 2 := by
  have hb := perturb_factor_lower D E hD hE ht hu q y
  have hp : 0 < 1+t*D q y+u*E q y := by linarith
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  linarith [hE q y]

omit [Fintype Ω] in
theorem perturbScore_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω L) :
    |perturbScore D E t u y| ≤ 2*n := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ q, |E q y / (1+t*D q y+u*E q y)|) ≤ ∑ _q : Fin n, (2:ℝ) :=
      Finset.sum_le_sum (fun q _ => perturb_fraction_bound D E hD hE ht hu q y)
    _ = _ := by simp [mul_comm]

end DilutedSpinGlass.KernelTower

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

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

omit [Fintype Ω] in
theorem measurable_perturbLog {L n : ℕ}
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbLog (base x) (D x) (E x) (t x) (u x) y) := by
  apply (hbase y).add
  apply Finset.measurable_sum
  intro q _
  exact ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y))).log

omit [Fintype Ω] in
theorem measurable_perturbScore {L n : ℕ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbScore (D x) (E x) (t x) (u x) y) := by
  apply Finset.measurable_sum
  intro q _
  exact (hE q y).div ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y)))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

variable {I : Type*} {X : I → Type*} [MeasurableSpace I]
  [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace I] in
theorem measurable_sigmaUncurry {Y : Type*} [MeasurableSpace Y] {f : (i : I) → X i → Y}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x : Sigma X => f x.1 x.2) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro i
  rw [← MeasurableSpace.comap_le_iff_le_map]
  rw [MeasurableSpace.comap_comp]
  exact (hf i).comap_le

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {I : Type*} {X : I → Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [∀ i, MeasurableSpace (X i)]
    (μ : Measure I) (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]

/-- Sufficient integrability on the genuine disjoint-union root law. -/
theorem familyLaw_integrable_bound (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i)) {B : I → ℝ} (hB : Integrable B μ)
    (hb : ∀ i x, |f i x| ≤ B i) :
    Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) := by
  let F : Sigma X → ℝ := fun z => f z.1 z.2
  have hm : Measurable F := measurable_sigmaUncurry hf
  have hi (i : I) : Integrable (f i) (ν i) :=
    Integrable.of_bound (hf i).aestronglyMeasurable (B i) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb i x))
  have hi' (i : I) : Integrable F (familyKernel ν i) := by
    change Integrable F ((ν i).map (Sigma.mk i))
    exact (integrable_map_measure hm.aestronglyMeasurable (measurable_sigmaMk i).aemeasurable).mpr (hi i)
  apply (Measure.integrable_comp_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi', ?_⟩
  apply hB.mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  change (∫ z, ‖F z‖ ∂(ν i).map (Sigma.mk i)) ≤ B i
  rw [integral_map (measurable_sigmaMk i).aemeasurable hm.norm.aestronglyMeasurable]
  have hh := integral_mono (hi i).norm (integrable_const (B i))
    (fun x => by simpa only [Real.norm_eq_abs] using hb i x)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

omit [∀ i, IsProbabilityMeasure (ν i)] in
 
theorem integral_familyLaw (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hi : Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν)) :
    (∫ z : Sigma X, f z.1 z.2 ∂familyLaw μ ν) = ∫ i, ∫ x, f i x ∂ν i ∂μ := by
  unfold familyLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ i, ∫ z : Sigma X, f z.1 z.2 ∂(ν i).map (Sigma.mk i) ∂μ) = _
  apply integral_congr_ae
  apply ae_of_all
  intro i
  exact integral_map (measurable_sigmaMk i).aemeasurable
    (measurable_sigmaUncurry hf).aestronglyMeasurable

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_memLp_linear {f : (n : ℕ) → X n → ℝ}
    (hf : ∀ n, Measurable (f n)) {A B : ℝ} (hb : ∀ n x, |f n x| ≤ A+B*n) :
    MemLp (fun z : Sigma X => f z.1 z.2) 2 (familyLaw (poissonMeasure r) ν) := by
  apply (memLp_two_iff_integrable_sq (measurable_sigmaUncurry hf).aestronglyMeasurable).mpr
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n x => (f n x)^2) (fun n => (hf n).pow_const 2)
    (B := fun n => 2*A^2+2*B^2*(n : ℝ)^2)
  · apply poisson_integrable_quadratic r (A := 2*A^2) (B := 2*B^2)
    intro n
    rw [abs_of_nonneg (by positivity)]
  · intro n x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : (f n x)^2 ≤ (A+B*n)^2 := by
      exact sq_le_sq' (abs_le.mp (hb n x)).1 (abs_le.mp (hb n x)).2
    nlinarith [sq_nonneg (A-B*n)]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_memLp :
    MemLp (fun z : Sigma X => (z.1 : ℝ)) 2 (familyLaw (poissonMeasure r) ν) := by
  apply familyPoisson_memLp_linear ν r (fun _ => measurable_const) (A := 0) (B := 1)
  intro n x
  simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousMarks
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
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- Adding a type uses its own prior, independently of all old marks. -/
theorem tower_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (split roots i) L (tower (Fin.cons i roots) L T Q) =
      KernelTower.prod L (tower roots L T Q) (markPrior L (Q i)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro z
      change T.1.weight z.1.1 *
          (∏ j : Fin (k+1), (Q ((Fin.cons i roots : Fin (k+1) → I) j) 0).weight
            ((Fin.cons z.2 z.1.2 : Row (A := A) (Fin.cons i roots)) j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      rw [Fin.prod_univ_succ]
      change T.1.weight z.1.1 *
        ((Q i 0).weight z.2 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      ring
    · funext z
      exact ih (T.2 z.1.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    physical roots L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      physical (Fin.cons i roots) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) =
      (y.1.1, physical (Fin.cons i roots) L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_succ {k : ℕ} (roots : Fin k → I) (i : I) (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    mark q L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      mark q.succ L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 q.succ, mark q L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) = (y.1.2 q.succ, mark q.succ L y.2)
    rw [ih]
    rfl

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_zero {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y) = mark 0 L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 0, KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y.2)) =
      (y.1.2 0, mark 0 L y.2)
    rw [ih]
    rfl

variable {k L : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem insertedLog_split (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (i : I)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    insertedLog base roots factor i (KernelTower.pathEquiv (split roots i) L y) =
      logWeight base (Fin.cons i roots) factor y := by
  simp only [insertedLog, logWeight, physical_split, mark_split_succ,
    mark_split_zero, Fin.sum_univ_succ]
  change base (physical (Fin.cons i roots) L y) +
      (∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y))) +
      Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) =
    base (physical (Fin.cons i roots) L y) +
      (Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) +
      ∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y)))
  ring

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountableReservoir
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.CountableReservoir
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {I : Type} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

theorem integrable_row {n : ℕ} {f : (Fin n → I) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) : Integrable f (Measure.pi (fun _ : Fin n => ν)) := by
  apply (integrable_const B).mono' (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hf x)

end DilutedSpinGlass.CountableReservoir

namespace DilutedSpinGlass.CountableReservoir
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {I : Type} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

omit [Countable I] [MeasurableSingletonClass I] in
/-- The countable root labels are genuinely iid under finite permutations. -/
theorem integral_pi_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : (Fin n → I) → ℝ) :
    (∫ roots, f (roots ∘ σ) ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ roots, f roots ∂Measure.pi (fun _ : Fin n => ν) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) σ).symm.integral_comp' f
  exact h

/-- A new label has precisely the same independent law as each old label. -/
theorem integral_pi_cons (n : ℕ) (f : (Fin (n+1) → I) → ℝ) {B : ℝ}
    (hf : ∀ roots, |f roots| ≤ B) :
    (∫ roots, f roots ∂Measure.pi (fun _ : Fin (n+1) => ν)) =
      ∫ i, ∫ roots, f (Fin.cons i roots) ∂Measure.pi (fun _ : Fin n => ν) ∂ν := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm.integral_comp' f
  have he : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => I) 0).symm :
      I × (Fin n → I) → (Fin (n+1) → I)) =
      (fun z : I × (Fin n → I) => Fin.cons z.1 z.2) := by
    funext labels
    exact Fin.insertNth_zero' labels.1 labels.2
  rw [he] at h
  rw [← h]
  apply integral_prod
  apply (integrable_const B).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hf (Fin.cons z.1 z.2))

omit [Countable I] [MeasurableSingletonClass I] in
theorem integral_pi_equivariant {n : ℕ} (F : (Fin n → I) → Fin n → ℝ)
    (hF : ∀ (σ : Equiv.Perm (Fin n)) roots q, F (roots ∘ σ) q = F roots (σ q))
    (q q' : Fin n) :
    (∫ roots, F roots q ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ roots, F roots q' ∂Measure.pi (fun _ : Fin n => ν) := by
  classical
  rw [← integral_pi_perm ν (Equiv.swap q q') (fun roots => F roots q)]
  apply integral_congr_ae
  exact ae_of_all _ (fun roots => by
    dsimp only
    rw [hF, Equiv.swap_apply_left])

/-- Palm for the full shared countable reservoir. It does not delete the
selected type or truncate the other types in the remaining law. -/
theorem poisson_add_label (s : ℝ≥0)
    (F : (n : ℕ) → (Fin n → I) → Fin n → ℝ) {B : ℝ}
    (hB : ∀ n roots q, |F n roots q| ≤ B)
    (hF : ∀ n (σ : Equiv.Perm (Fin n)) roots q, F n (roots ∘ σ) q = F n roots (σ q)) :
    (∫ n : ℕ, ∫ roots, ∑ q, F n roots q
      ∂Measure.pi (fun _ : Fin n => ν) ∂poissonMeasure s) =
      (s : ℝ) * ∫ n : ℕ, ∫ i, ∫ roots, F (n+1) (Fin.cons i roots) 0
        ∂Measure.pi (fun _ : Fin n => ν) ∂ν ∂poissonMeasure s := by
  let a : ℕ → ℝ := fun n => if h : 0 < n then
    ∫ roots, F n roots ⟨0,h⟩ ∂Measure.pi (fun _ : Fin n => ν) else 0
  have ha (n : ℕ) : a (n+1) =
      ∫ roots, F (n+1) roots 0 ∂Measure.pi (fun _ : Fin (n+1) => ν) := by
    simp only [a, Nat.zero_lt_succ, ↓reduceDIte]
    rfl
  have hsum (n : ℕ) :
      (∫ roots, ∑ q, F n roots q ∂Measure.pi (fun _ : Fin n => ν)) = (n : ℝ)*a n := by
    rw [integral_finsetSum _ (fun q _ => integrable_row ν (fun roots => hB n roots q))]
    by_cases hn : 0 < n
    · simp only [a, dite_eq_left hn]
      rw [show (fun q : Fin n => ∫ roots, F n roots q ∂Measure.pi (fun _ : Fin n => ν)) =
        (fun _ : Fin n => ∫ roots, F n roots ⟨0,hn⟩ ∂Measure.pi (fun _ : Fin n => ν)) from
          funext (fun q => integral_pi_equivariant ν (F n) (hF n) q ⟨0,hn⟩)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp
  have hi : Integrable (fun n => a (n+1)) (poissonMeasure s) := by
    apply poisson_integrable_linear s (A := B) (B := 0)
    intro n
    rw [ha]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one, zero_mul, add_zero] using
      (norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin (n+1) => ν))
        (f := fun roots => F (n+1) roots 0) (C := B)
        (ae_of_all _ (fun roots => by simpa only [Real.norm_eq_abs] using hB (n+1) roots 0)))
  simp_rw [hsum]
  rw [poisson_add_one s a hi]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    rw [ha]
    exact integral_pi_cons ν n (fun roots => F (n+1) roots 0) (fun roots => hB (n+1) roots 0))

end DilutedSpinGlass.CountableReservoir

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkInsertion
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
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

theorem tower_transport {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (rowPerm roots σ) L (tower roots L T Q) =
      tower (roots ∘ σ) L T Q := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro x
      change T.1.weight x.1 * (∏ q, (Q (roots q) 0).weight
          (Equiv.piCongrLeft (fun q => A (roots q)) σ x.2 q)) =
        T.1.weight x.1 * ∏ q, (Q (roots (σ q)) 0).weight (x.2 q)
      congr 1
      symm
      exact Fintype.prod_equiv σ _ _ (fun q => by rw [Equiv.piCongrLeft_apply_apply])
    · funext x
      exact ih (T.2 x.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical (roots ∘ σ) L (KernelTower.pathEquiv (rowPerm roots σ) L y) =
      physical roots L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical (roots ∘ σ) L (KernelTower.pathEquiv (rowPerm roots σ) L y.2)) =
      (y.1.1, physical roots L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) L) (q : Fin k) :
    mark q L (KernelTower.pathEquiv (rowPerm roots σ) L y) = mark (σ q) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 (σ q), mark q L (KernelTower.pathEquiv (rowPerm roots σ) L y.2)) =
      (y.1.2 (σ q), mark (σ q) L y.2)
    rw [ih]

variable {k L : ℕ}
omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem logWeight_rowPerm (roots : Fin k → I) (σ : Equiv.Perm (Fin k))
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    logWeight base (roots ∘ σ) factor (KernelTower.pathEquiv (rowPerm roots σ) L y) =
      logWeight base roots factor y := by
  simp only [logWeight, physical_rowPerm, mark_rowPerm, Function.comp_apply]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

theorem treeScore_perm (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (σ : Equiv.Perm (Fin k)) (q : Fin k) :
    treeScore S a T Q m base (roots ∘ σ) factor numerator f q =
      treeScore S a T Q m base roots factor numerator f (σ q) := by
  have h := PrescribedTree.tiltedSampleExpect_transport (rowPerm roots σ) S (tower roots L T Q) m
    (logWeight base (roots ∘ σ) factor) (fun x =>
      f (fun b => physical (roots ∘ σ) L (S.pathAt b x)) *
        (numerator (roots (σ q)) (physical (roots ∘ σ) L (S.pathAt a x)) (mark q L (S.pathAt a x)) /
          factor (roots (σ q)) (physical (roots ∘ σ) L (S.pathAt a x)) (mark q L (S.pathAt a x))))
  have heq : logWeight base (roots ∘ σ) factor ∘ KernelTower.pathEquiv (rowPerm roots σ) L =
      logWeight base roots factor := funext (fun y => logWeight_rowPerm roots σ base factor y)
  rw [heq] at h
  rw [tower_transport] at h
  refine h.trans ?_
  apply congrArg
  funext x
  simp only [Function.comp_apply, PrescribedTree.pathAt_sampleEquiv, physical_rowPerm, mark_rowPerm]

theorem abs_treeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin k) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i y z, |numerator i y z| ≤ 1)
    (hA : ∀ i y z, 1/2 ≤ factor i y z) :
    |treeScore S a T Q m base roots factor numerator f q| ≤ 2*B := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul, abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num) (hA _ _ _))]
  have hd : |numerator (roots q) (physical roots L (S.pathAt a x))
      (mark q L (S.pathAt a x))| /
      factor (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x)) ≤ 2 := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hA _ _ _))]
    linarith [hn (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x)),
      hA (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x))]
  calc
    _ ≤ |f (fun b => physical roots L (S.pathAt b x))| * 2 :=
      mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ ≤ B * 2 := mul_le_mul_of_nonneg_right (hf _) (by norm_num)
    _ = 2 * B := mul_comm _ _

end DilutedSpinGlass.HeterogeneousMarks



namespace DilutedSpinGlass.HeterogeneousMarks
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {k L : ℕ}

/-- Literal change-of-variables and successive-tilt proof of the Palm insertion.
No conditional factorization of the tilted mark rows is being assumed. -/
theorem treeScore_insertion (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    treeScore S a T Q m base (Fin.cons i roots) factor numerator f 0 =
      insertedTreeScore S a T Q m base roots i factor numerator f := by
  have h := PrescribedTree.tiltedSampleExpect_transport (split roots i) S
    (tower (Fin.cons i roots) L T Q) m (insertedLog base roots factor i)
    (fun x => f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
      (numerator i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
        (KernelTower.pathSnd L (S.pathAt a x)) /
        factor i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
          (KernelTower.pathSnd L (S.pathAt a x))))
  have heq : insertedLog base roots factor i ∘
      KernelTower.pathEquiv (split roots i) L = logWeight base (Fin.cons i roots) factor :=
    funext (fun y => insertedLog_split base roots factor i y)
  rw [heq, tower_split] at h
  have ht : KernelTower.tilt L (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) m
      (insertedLog base roots factor i) =
      KernelTower.tilt L (KernelTower.prod L
        (KernelTower.tilt L (tower roots L T Q) m (logWeight base roots factor))
        (markPrior L (Q i))) m
        (fun y => Real.log (factor i (physical roots L (KernelTower.pathFst L y))
          (KernelTower.pathSnd L y))) := by
    rw [← KernelTower.tilt_prod_fst L (tower roots L T Q) (markPrior L (Q i)) m
      (logWeight base roots factor), KernelTower.tilt_insertion]
    rfl
  rw [ht] at h
  simp only [Function.comp_def, PrescribedTree.pathAt_sampleEquiv,
    physical_split, mark_split_zero] at h
  change _ = insertedTreeScore S a T Q m base roots i factor numerator f
  exact h.symm

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

/-- Full countable-type Palm for the literal tilted tree statistic. Its right
side uses the same original reservoir, plus one independently sampled mark. -/
theorem full_reservoir_palm {L : ℕ} (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i y z, |numerator i y z| ≤ 1)
    (hA : ∀ i y z, 1/2 ≤ factor i y z) :
    (∫ n : ℕ, ∫ roots, ∑ q, treeScore S a T Q m base roots factor numerator f q
      ∂Measure.pi (fun _ : Fin n => ν) ∂poissonMeasure s) =
      (s : ℝ) * ∫ n : ℕ, ∫ i, ∫ roots,
        insertedTreeScore S a T Q m base roots i factor numerator f
          ∂Measure.pi (fun _ : Fin n => ν) ∂ν ∂poissonMeasure s := by
  rw [CountableReservoir.poisson_add_label ν s
    (fun n roots q => treeScore S a T Q m base roots factor numerator f q)
    (fun _ roots q => abs_treeScore_le S a T Q m base roots factor numerator f q hf hn hA)
    (fun _ σ roots q => treeScore_perm S a T Q m base roots factor numerator f σ q)]
  simp_rw [treeScore_insertion]

end DilutedSpinGlass.HeterogeneousMarks

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

/-- The full cancellation calculus, with a moving test. Fresh branches are
sampled genuinely, not defined by their expectation. -/
theorem hasDerivAt_fullyProtected_varying {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) {G : ℝ → Sample Ω S → ℝ} {G' : Sample Ω S → ℝ} (u : ℝ)
    (hu : ∀ y, 0 < 1+u*D y) (hG : ∀ x, HasDerivAt (fun t => G t x) (G' x) u) :
    HasDerivAt (fun t => fullyProtected S T m D (G t) t)
      (fullyProtected S T m D G' u +
       ∑ v : Internal S, gamma S m v *
        fullyProtected (grow S v) T m D (fun x => G u (oldSample S v x) * D (newPath S v x)) u) u := by
  classical
  let f (t : ℝ) (y : FinitePath Ω n) := Real.log (1+t*D y)
  let DL (y : FinitePath Ω n) := D y / (1+u*D y)
  have hf (y : FinitePath Ω n) : HasDerivAt (fun t => f t y) (DL y) u :=
    hasDerivAt_log_affine (ne_of_gt (hu y))
  have hproto := hasDerivAt_protected_expect S T m hm hroot Finset.univ (G u) hf
  have hvar := hasDerivAt_protected_expect_varying S T m hm hroot Finset.univ hf hG
  have hfull := hasDerivAt_fullyProtected S T m hm hroot hend D (G u) u hu
  have heq (H : Sample Ω S → ℝ) (t : ℝ) :
      (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
        (fun x => H x * Real.exp (-protectedLog S Finset.univ (f t) x)) =
        fullyProtected S T m D H t := by
    apply FiniteLaw.expect_congr
    intro x
    rw [leafSum_eq_sum]
    rfl
  simp_rw [heq] at hproto hvar
  have hconst := hproto.unique hfull
  rw [hconst] at hvar
  exact hvar

theorem fullyProtected_sum {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ)
    {ι : Type} (A : Finset ι) (G : ι → Sample Ω S → ℝ) (t : ℝ) :
    fullyProtected S T m D (fun x => ∑ i ∈ A, G i x) t =
      ∑ i ∈ A, fullyProtected S T m D (G i) t := by
  unfold fullyProtected
  simp only [Finset.sum_mul, FiniteLaw.expect_sum]

 
theorem hasDerivAt_anchorEval {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι]
    (A : Finset ι) (U : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) (u : ℝ) (hu : ∀ y, 0 < 1+u*D y) :
    HasDerivAt (anchorEval S T m D A U G)
      ((∑ i ∈ A, anchorEval S T m D (A.erase i) U (fun x => G x * D (U i x)) u) +
       ∑ v : Internal S, gamma S m v * anchorEval (grow S v) T m D A
        (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) u) u := by
  have hprod (x : Sample Ω S) :
      HasDerivAt (fun t : ℝ => G x * ∏ i ∈ A, (1+t*D (U i x)))
        (∑ i ∈ A, (G x * D (U i x)) * ∏ j ∈ A.erase i, (1+u*D (U j x))) u := by
    have hh := (HasDerivAt.fun_finsetProd (u := A) (fun i _ =>
      (((hasDerivAt_id u).mul_const (D (U i x))).const_add 1))).const_mul (G x)
    apply hh.congr_deriv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_eq_mul, id_eq, one_mul]
    ring
  have hd := hasDerivAt_fullyProtected_varying S T m hm hroot hend D u hu hprod
  apply hd.congr_deriv
  rw [fullyProtected_sum]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro v _
    apply congrArg (gamma S m v * ·)
    apply FiniteLaw.expect_congr
    intro x
    change ((G (oldSample S v x) * ∏ i ∈ A, (1+u*D (U i (oldSample S v x)))) *
      D (newPath S v x)) * _ = _
    ring

/-- Every derivative order of the actual finite-kernel canceled-anchor
expectation is the ordered old-or-fresh extension sum. -/
theorem hasDerivAt_anchorIterate {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι]
    (k : ℕ) (S : PrescribedTree n) (A : Finset ι)
    (U : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    (u : ℝ) (hu : ∀ y, 0 < 1+u*D y) :
    HasDerivAt (anchorIterate T m D k S A U G)
      (anchorIterate T m D (k+1) S A U G u) u := by
  induction k generalizing S A with
  | zero => exact hasDerivAt_anchorEval S T m hm hroot hend D A U G u hu
  | succ k ih =>
    have h₁ := HasDerivAt.sum (u := A) (fun i (_ : i ∈ A) =>
      ih S (A.erase i) U (fun x => G x * D (U i x)))
    have h₂ := HasDerivAt.sum (u := Finset.univ) (fun v (_ : v ∈ (Finset.univ : Finset (Internal S))) =>
      (ih (grow S v) A (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x))).const_mul (gamma S m v))
    apply (h₁.add h₂).congr_of_eventuallyEq
    filter_upwards [] with t
    simp only [Pi.add_apply, Finset.sum_apply]
    rfl

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

namespace DilutedSpinGlass.PrescribedTree

variable {Ω : Type} [Fintype Ω]

theorem abs_freshEval_le {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (v : Internal S) (D : FinitePath Ω n → ℝ) {B : ℝ} (hD : ∀ y, |D y| ≤ B)
    (x : Sample Ω S) : |freshEval S T v D x| ≤ B := by
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact (KernelTower.law (n+1) T).abs_expect_le hD
    | some v => exact ih v.1 (T.2 (x v.1).1) v.2 _ (fun y => hD _) (x v.1).2

theorem abs_vertexScore_le {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (f D : FinitePath Ω n → ℝ) {B : ℝ} (hD : ∀ y, |D y| ≤ B)
    (x : Sample Ω S) : |vertexScore S T m f D x| ≤ 2 * (leaves S:ℝ) * B := by
  rw [vertexScore_decomposition, hend, one_mul]
  apply (abs_add_le _ _).trans
  have hleaf : |∑ a : Leaf S, D (pathAt S a x)| ≤ (leaves S:ℝ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ a : Leaf S, |D (pathAt S a x)|) ≤ ∑ _a : Leaf S, B :=
        Finset.sum_le_sum (fun a _ => hD _)
      _ = _ := by simp
  have hfresh : |∑ v : Internal S, gamma S m v *
      freshEval S (KernelTower.tilt n T (fun j => m j.succ) f) v D x| ≤ (leaves S:ℝ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ v : Internal S, |gamma S m v * freshEval S (KernelTower.tilt n T (fun j => m j.succ) f) v D x|)
        ≤ ∑ v : Internal S, |gamma S m v| * B := by
          apply Finset.sum_le_sum
          intro v _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_freshEval_le S _ v D hD x) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, sum_abs_gamma S m hm hpos hroot hend]
  linarith

omit [Fintype Ω] in
theorem exp_neg_leafSum_log {n : ℕ} (S : PrescribedTree n)
    (A : FinitePath Ω n → ℝ) (hA : ∀ y, 0 < A y) (x : Sample Ω S) :
    Real.exp (-leafSum S (fun y => Real.log (A y)) x) =
      (∏ a : Leaf S, A (pathAt S a x))⁻¹ := by
  rw [leafSum_eq_sum, Real.exp_neg, Real.exp_sum]
  congr 1
  exact Finset.prod_congr rfl (fun a _ => Real.exp_log (hA _))

/-- Links the proved ordered history derivative rule to the single canceled
anchor of the manuscript, not a different protected-leaf functional. -/
theorem anchorEval_eq_anchorInsertion {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ)
    (a : Leaf S) (G : Sample Ω S → ℝ) (t : ℝ) (ht : ∀ y, 0 < 1+t*D y) :
    anchorEval S T m D (Finset.univ.erase a) (pathAt S) G t =
      anchorInsertion S T m a G (fun y => 1+t*D y) := by
  classical
  apply FiniteLaw.expect_congr
  intro x
  rw [exp_neg_leafSum_log S _ ht]
  have hp := Finset.mul_prod_erase (Finset.univ : Finset (Leaf S))
    (fun b => 1+t*D (pathAt S b x)) (Finset.mem_univ a)
  have hn : ∏ b ∈ (Finset.univ : Finset (Leaf S)).erase a, (1+t*D (pathAt S b x)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => ne_of_gt (ht _))
  rw [← hp]
  field_simp

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

theorem hasDerivAt_anchorInsertion {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (a : Leaf S) (G : Sample Ω S → ℝ)
    {A : ℝ → FinitePath Ω n → ℝ} {E : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, HasDerivAt (fun t => A t y) (E y) u)
    (hp : ∀ y, 0 < A u y) :
    HasDerivAt (fun t => anchorInsertion S T m a G (A t))
      (anchorDerivative S T m a G (A u) E) u := by
  have hf (y : FinitePath Ω n) := (hA y).log (ne_of_gt (hp y))
  have hg (x : Sample Ω S) := (hasDerivAt_const u (G x)).div
    (hA (pathAt S a x)) (ne_of_gt (hp (pathAt S a x)))
  have hd := hasDerivAt_sampleLaw_tilt_expect S T m hm hroot hf hg
  apply hd.congr_deriv
  apply FiniteLaw.expect_congr
  intro x
  change (0 * A u (pathAt S a x) - G x * E (pathAt S a x)) / A u (pathAt S a x)^2 +
    G x / A u (pathAt S a x) * vertexScore S T m (fun y => Real.log (A u y))
      (fun y => E y / A u y) x = _
  ring

private theorem abs_div_bound {x y B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B)
    (hy : (1:ℝ)/2 ≤ y) : |x/y| ≤ 2*B := by
  have hyp : 0 < y := by linarith
  rw [abs_div, abs_of_pos hyp, div_le_iff₀ hyp]
  nlinarith

/-- Uniform bound in the auxiliary `u` direction. It uses only probability
normalization and the telescoping absolute tree coefficients. -/
theorem abs_anchorDerivative_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (hroot : m 0 = 0)
    (hend : m (Fin.last n) = 1) (a : Leaf S) (G : Sample Ω S → ℝ)
    (A E : FinitePath Ω n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ x, |G x| ≤ B) (hA : ∀ y, (1:ℝ)/2 ≤ A y) (hE : ∀ y, |E y| ≤ 1) :
    |anchorDerivative S T m a G A E| ≤ (4+8*(leaves S:ℝ))*B := by
  have hEA (y : FinitePath Ω n) : |E y / A y| ≤ 2 := by
    simpa using abs_div_bound (by norm_num : (0:ℝ)≤1) (hE y) (hA y)
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul]
  have hs := abs_vertexScore_le S T m hm hpos hroot hend (fun y => Real.log (A y))
    (fun y => E y/A y) hEA x
  have hdiff := (abs_sub _ _).trans (add_le_add hs (hEA (pathAt S a x)))
  have hG' := abs_div_bound hB (hG x) (hA (pathAt S a x))
  apply (mul_le_mul hG' hdiff (abs_nonneg _) (by positivity)).trans_eq
  ring

omit [Fintype Ω] in
private theorem affine_two_lower_half {n : ℕ} (D E : FinitePath Ω n → ℝ)
    (hD : ∀ y, |D y| ≤ 1) (hE : ∀ y, |E y| ≤ 1) {t u : ℝ}
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω n) :
    (1:ℝ)/2 ≤ 1+t*D y+u*E y := by
  have ht' : |t*D y| ≤ 1/4 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hD y) (abs_nonneg t)).trans (by simpa using ht)
  have hu' : |u*E y| ≤ 1/4 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hE y) (abs_nonneg u)).trans (by simpa using hu)
  linarith [(abs_le.mp ht').1, (abs_le.mp hu').1]

/-- The `u`-error in pert:analytic is uniformly linear, before any root
averaging. No analyticity or enlargement of computational limits is needed. -/
theorem anchorInsertion_sub_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (a : Leaf S) (G : Sample Ω S → ℝ) (D E : FinitePath Ω n → ℝ)
    {B t u : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B)
    (hD : ∀ y, |D y| ≤ 1) (hE : ∀ y, |E y| ≤ 1)
    (ht : |t| ≤ 1/4) (huz : 0 ≤ u) (hu : u ≤ 1/4) :
    |anchorInsertion S T m a G (fun y => 1+t*D y+u*E y) -
      anchorInsertion S T m a G (fun y => 1+t*D y)| ≤ (4+8*(leaves S:ℝ))*B*u := by
  let F (v : ℝ) := anchorInsertion S T m a G (fun y => 1+t*D y+v*E y)
  let F' (v : ℝ) := anchorDerivative S T m a G (fun y => 1+t*D y+v*E y) E
  have hlow (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) u) (y : FinitePath Ω n) :
      (1:ℝ)/2 ≤ 1+t*D y+v*E y :=
    affine_two_lower_half D E hD hE ht (by rw [abs_of_nonneg hv.1]; exact hv.2.trans hu) y
  have hd (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) u) : HasDerivAt F (F' v) v := by
    apply hasDerivAt_anchorInsertion S T m hm hroot a G
    · intro y
      simpa using ((hasDerivAt_id v).mul_const (E y)).const_add (1+t*D y)
    · intro y
      linarith [hlow v hv y]
  have hb (v : ℝ) (hv : v ∈ Set.Ico (0:ℝ) u) : ‖F' v‖ ≤ (4+8*(leaves S:ℝ))*B := by
    rw [Real.norm_eq_abs]
    exact abs_anchorDerivative_le S T m hmono hpos hroot hend a G _ E hB hG
      (hlow v ⟨hv.1,hv.2.le⟩) hE
  have hx := norm_image_sub_le_of_norm_deriv_le_segment' (fun v hv => (hd v hv).hasDerivWithinAt)
    hb u (show u ∈ Set.Icc (0:ℝ) u from ⟨huz,le_rfl⟩)
  simpa only [F, zero_mul, add_zero, sub_zero, Real.norm_eq_abs] using hx

end DilutedSpinGlass.PrescribedTree

open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass

/-- Identifies an explicitly constructed differential jet with Mathlib's
iterated derivatives, without any analytic or compactness assumption. -/
theorem jet_iteratedDerivWithin {F : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s)
    (hF : ∀ k x, x ∈ s → HasDerivAt (F k) (F (k+1) x) x)
    (k : ℕ) : EqOn (iteratedDerivWithin k (F 0) s) (F k) s := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih hx)]
    exact (hF k x hx).hasDerivWithinAt.derivWithin (hs x hx)

theorem jet_contDiffOn {F : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s)
    (hF : ∀ k x, x ∈ s → HasDerivAt (F k) (F (k+1) x) x)
    (k : ℕ) : ContDiffOn ℝ k (F 0) s := by
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs).mpr
  have hd (j : ℕ) : DifferentiableOn ℝ (F j) s :=
    fun x hx => (hF j x hx).differentiableAt.differentiableWithinAt
  constructor
  · intro j _
    exact (hd j).continuousOn.congr (jet_iteratedDerivWithin hs hF j)
  · intro j _
    exact (hd j).congr (jet_iteratedDerivWithin hs hF j)

/-- Uniform finite Taylor remainder for the explicit jet used in the
canceled-anchor identities. Only a bound on the required derivative enters. -/
theorem jet_taylor_bound {F : ℕ → ℝ → ℝ} {a b t C : ℝ} (hab : a < b)
    (hF : ∀ k x, x ∈ Icc a b → HasDerivAt (F k) (F (k+1) x) x)
    (k : ℕ) (ht : t ∈ Icc a b)
    (hC : ∀ x ∈ Icc a b, |F (k+1) x| ≤ C) :
    |F 0 t - ∑ j ∈ Finset.range (k+1), F j a / (j.factorial:ℝ) * (t-a)^j| ≤
      C * (t-a)^(k+1) / (k.factorial:ℝ) := by
  have hs := uniqueDiffOn_Icc hab
  have hbound := taylor_mean_remainder_bound hab.le (jet_contDiffOn hs hF (k+1)) ht
    (by
      intro x hx
      rw [Real.norm_eq_abs, jet_iteratedDerivWithin hs hF (k+1) hx]
      exact hC x hx)
  rw [taylor_within_apply] at hbound
  simp only [Real.norm_eq_abs] at hbound
  convert hbound using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [jet_iteratedDerivWithin hs hF j (left_mem_Icc.mpr hab.le)]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Quantitative real Taylor expansion of the actual canceled-anchor
insertion. This is uniform in every probability kernel and can therefore
be root-averaged before selecting any subsequence. -/
theorem anchorInsertion_taylor_bound {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    (a : Leaf S) (G : Sample Ω S → ℝ) {B t : ℝ}
    (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) (k : ℕ) :
    |anchorInsertion S T m a G (fun y => 1+t*D y) -
      ∑ j ∈ Finset.range (k+1), anchorCoefficient S T m D a G j * t^j| ≤
        (B * derivativeBound (leaves S + (Finset.univ.erase a).card) (k+1) /
          (k.factorial:ℝ)) * t^(k+1) := by
  let F (j : ℕ) := anchorIterate T m D j S (Finset.univ.erase a) (pathAt S) G
  have hd (j : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/2)) :
      HasDerivAt (F j) (F (j+1) x) x := by
    apply hasDerivAt_anchorIterate T m hm hroot hend D j S _ _ _
    intro y
    have hx' : |x| ≤ 1/2 := by simpa only [abs_of_nonneg hx.1] using hx.2
    have hh := mul_le_mul_of_nonneg_left (hD y) (abs_nonneg x)
    rw [← abs_mul, mul_one] at hh
    have := (abs_le.mp (hh.trans hx')).1
    linarith
  have hb (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/2)) :
      |F (k+1) x| ≤ B*derivativeBound (leaves S+(Finset.univ.erase a).card) (k+1) := by
    apply abs_anchorIterate_le T m hmono hpos hroot hend D hD (k+1) S _ _ _ hB hG
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hr := jet_taylor_bound (by norm_num : (0:ℝ)<1/2) hd k ht hb
  have ha : F 0 t = anchorInsertion S T m a G (fun y => 1+t*D y) := by
    apply anchorEval_eq_anchorInsertion
    intro y
    have hh := mul_le_mul_of_nonneg_left (hD y) (abs_nonneg t)
    rw [← abs_mul, mul_one, abs_of_nonneg ht.1] at hh
    have := (abs_le.mp (hh.trans ht.2)).1
    linarith
  rw [ha] at hr
  simpa only [F, anchorCoefficient, sub_zero, div_mul_eq_mul_div] using hr

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

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

/-- Quadratic envelopes allow both the pressure and its square to be passed
through the two independent compound laws, without any count cut-off. -/
theorem fullRoot_integrable_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (packRoot F) (fullRootLaw ξ μ ν r s) := by
  have hk := (((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)).comp_snd (rootLaw M ξ)
  have hn := (((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)
  have he : Integrable (fun z : FullRootState Y X I M => B+C*(z.2.1.1:ℝ)^2+D*(z.2.2.1:ℝ)^2)
      (fullRootLaw ξ μ ν r s) := (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' (measurable_packRoot hF).aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,packRoot] using hb z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))


theorem twoCompound_integrable_quadratic
    {F : (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2))
    {B C D : ℝ} (hb : ∀ k x n y, |F k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2)
      ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) := by
  have hk := ((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)
  have hn := ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)
  have he : Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      B+C*(z.1.1:ℝ)^2+D*(z.2.1:ℝ)^2) ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) :=
    (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' hF.aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using hb z.1.1 z.1.2 z.2.1 z.2.2))

/-- Exact Fubini identity for the full root law, with all count-dependent
root spaces and all physical fields retained. -/
theorem integral_fullRootLaw_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, F h k x n y
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
          ∂poissonMeasure r ∂rootLaw M ξ := by
  have hm := measurable_packRoot hF
  rw [fullRootLaw,integral_prod _ (fullRoot_integrable_quadratic ξ μ ν r s hF hb)]
  apply integral_congr_ae
  apply ae_of_all
  intro h
  have hhm : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F h z.1.1 z.1.2 z.2.1 z.2.2) := hm.comp (measurable_const.prodMk measurable_id)
  have hhi := twoCompound_integrable_quadratic μ ν r s hhm (hb h)
  change (∫ z, F h z.1.1 z.1.2 z.2.1 z.2.2 ∂(compoundRootLaw μ r).prod (compoundRootLaw ν s)) = _
  rw [integral_prod _ hhi]
  have hg (k : ℕ) : Measurable (fun x : RootPath X k =>
      ∫ z : Sigma (RootPath I), F h k x z.1 z.2 ∂compoundRootLaw ν s) := by
    have hh : Measurable (fun z : RootPath X k × Sigma (RootPath I) => F h k z.1 z.2.1 z.2.2) :=
      hhm.comp (((measurable_sigmaMk k).comp measurable_fst).prodMk measurable_snd)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  change (∫ z : Sigma (RootPath X), ∫ w : Sigma (RootPath I),
    F h z.1 z.2 w.1 w.2 ∂compoundRootLaw ν s
      ∂familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))) = _
  rw [integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k x => ∫ z : Sigma (RootPath I), F h k x z.1 z.2 ∂compoundRootLaw ν s)
      hg hhi.integral_prod_left]
  apply integral_congr_ae
  apply ae_of_all
  intro k
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hfm (n : ℕ) : Measurable (F h k x n) :=
    (hF k n).comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  exact integral_familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
    (F h k x) hfm
    (familyLaw_integrable_bound (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
      (F h k x) hfm
      ((integrable_const (B+C*(k:ℝ)^2)).add ((poisson_integrable_count_sq s).const_mul D))
      (hb h k x))

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSteps
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} {A : I → Type} {L n : ℕ}

theorem selectedCoefficient_bound (roots : Fin n → I) (sel : I → Bool)
    (D : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (q : Fin n) (y : FinitePath (Ω × Row (A := A) roots) L) :
    |selectedCoefficient roots sel D q y| ≤ 1 := by
  unfold selectedCoefficient
  split
  · exact hD _ _ _
  · norm_num

/-- Every unselected term remains in the same log weight and the same finite
mark prior. This is an identity, not a distributional truncation. -/
theorem selected_perturbLog_eq (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.perturbLog (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      logWeight base roots (selectedFactor sel fixed D E t u) := by
  funext y
  unfold KernelTower.perturbLog otherLog logWeight
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  cases h : sel (roots q) <;> simp [selectedFactor,selectedCoefficient,h]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GeneralRootArrayLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

variable {X : Type} [MeasurableSpace X]

lemma rootArrayEquiv_apply (n : ℕ) (x : RootPath X n) : rootArrayEquiv (X := X) n x = rootArray n x := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change Fin.insertNth 0 x.1 (rootArrayEquiv (X := X) n x.2) =
      Fin.cons (α := fun _ : Fin (n+1) => X) x.1 (rootArray n x.2)
    rw [Fin.insertNth_zero', ih]


/-- Exact law identification for arbitrary measurable disorder alphabets,
including the continuous physical interaction tables and external fields. -/
theorem measurePreserving_rootArray (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (rootArrayEquiv (X := X) n) (rootLaw n (fun _ => μ))
      (Measure.pi (fun _ : Fin n => μ)) := by
  induction n with
  | zero =>
    refine ⟨(rootArrayEquiv 0).measurable, ?_⟩
    rw [rootLaw,Measure.map_dirac' (rootArrayEquiv 0).measurable,Measure.pi_of_empty]
    congr 1
  | succ n ih =>
    exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm.comp
      ((MeasurePreserving.id μ).prod ih)

theorem integral_rootArray_eq_pi (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) :
    (∫ x, f (rootArray n x) ∂rootLaw n (fun _ => μ)) =
      ∫ x, f x ∂Measure.pi (fun _ : Fin n => μ) := by
  simpa only [rootArrayEquiv_apply] using (measurePreserving_rootArray μ n).integral_comp' f

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_JointRootParam
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
variable {X I Y U : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] [MeasurableSpace U] {M : ℕ}

/-- Joint measurability through both random counts, with an external parameter. -/
theorem measurable_packRoot_param
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → U → ℝ}
    (hF : ∀ k n, Measurable (fun z : ((RootPath Y M × RootPath X k) × RootPath I n) × U => F z.1.1.1 k z.1.1.2 n z.1.2 z.2)) :
    Measurable (fun z : FullRootState Y X I M × U => packRoot (fun h k x n y => F h k x n y z.2) z.1) := by
  have hn (k : ℕ) : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × Sigma (RootPath I) =>
      F z.1.1.1 k z.1.1.2 z.2.1 z.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × RootPath X k) × U) n y => F z.1.1 k z.1.2 n y z.2)
      (fun n => (hF k n).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  have hk : Measurable (fun z : ((RootPath Y M × Sigma (RootPath I)) × U) × Sigma (RootPath X) =>
      F z.1.1.1 z.2.1 z.2.2 z.1.1.2.1 z.1.1.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × Sigma (RootPath I)) × U) k x => F z.1.1 k x z.1.2.1 z.1.2.2 z.2)
      (fun k => (hn k).comp (((measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd).prodMk measurable_fst.fst.snd))
  exact hk.comp (((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd).prodMk measurable_fst.snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

omit [MeasurableSpace U] in
theorem fullRoot_count_memLp :
    MemLp (fun z : FullRootState Y X I M => (z.2.2.1 : ℝ)) 2 (fullRootLaw ξ μ ν r s) := by
  exact ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)

end DilutedSpinGlass
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
open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass

theorem extractionProbe_pos (j : ℕ) : 0 < extractionProbe j := by
  unfold extractionProbe
  positivity

theorem extractionProbe_le_half (j : ℕ) : extractionProbe j ≤ 1/2 := by
  unfold extractionProbe
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg _
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+4)]
  linarith

theorem extractionProbe_tendsto : Tendsto extractionProbe atTop (𝓝 0) := by
  have hh : Tendsto (fun j : ℕ => (j:ℝ)+4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  change Tendsto (fun j : ℕ => 1 / ((j:ℝ)+4)) atTop (𝓝 0)
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hh

/-- Real finite-remainder extraction. This avoids both a complex normal-family
argument and a subsequence of limiting coefficients: all coefficients tend to
zero directly. The same base function is tested at every probe, as required by
the Poisson add-one identity. -/
theorem coefficients_tendsto_zero_of_uniform_remainders
    (H : ℕ → ℝ → ℝ) (a : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (C : ℝ)
    (_hB : ∀ k, 0 ≤ B k) (hC : 0 ≤ C)
    (hR : ∀ N k t, t ∈ Icc (0:ℝ) (1/2) →
      |H N t - ∑ i ∈ Finset.range (k+1), a N i * t^i| ≤ B k * t^(k+1))
    (err : ℕ → ℕ → ℝ) (herr : ∀ j, Tendsto (err j) atTop (𝓝 0))
    (hsmall : ∀ j N, |H N (extractionProbe j)| ≤
      C * extractionProbe j ^ (j+4) + err j N) :
    ∀ k, Tendsto (fun N => a N k) atTop (𝓝 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hlim : Tendsto (fun j => (C+B k)*extractionProbe j) atTop (𝓝 0) := by
      simpa only [mul_zero] using extractionProbe_tendsto.const_mul (C+B k)
    have he : ∀ᶠ j in atTop, (C+B k)*extractionProbe j < ε/2 :=
      hlim.eventually (eventually_lt_nhds (half_pos hε))
    obtain ⟨j, hjk, hjε⟩ := ((eventually_ge_atTop k).and he).exists
    let t := extractionProbe j
    have htpos : 0 < t := extractionProbe_pos j
    have hthalf : t ≤ 1/2 := extractionProbe_le_half j
    have htone : t ≤ 1 := by linarith
    let lower (N : ℕ) := ∑ i ∈ Finset.range k, a N i * t^i
    have hlower : Tendsto lower atTop (𝓝 0) := by
      have hh := tendsto_finsetSum (Finset.range k) (fun i hi =>
        (ih i (Finset.mem_range.mp hi)).mul_const (t^i))
      simpa only [zero_mul, Finset.sum_const_zero] using hh
    have htail : Tendsto (fun N => (err j N + |lower N|) / t^k) atTop (𝓝 0) := by
      simpa only [abs_zero, add_zero, zero_div] using ((herr j).add hlower.abs).div_const (t^k)
    have hetail : ∀ᶠ N in atTop, (err j N + |lower N|) / t^k < ε/2 :=
      htail.eventually (eventually_lt_nhds (half_pos hε))
    obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hetail
    refine ⟨N₀, fun N hN => ?_⟩
    have hTaylor := hR N k t ⟨htpos.le,hthalf⟩
    have hsplit : ∑ i ∈ Finset.range (k+1), a N i*t^i = lower N + a N k*t^k := by
      rw [Finset.sum_range_succ]
    rw [hsplit] at hTaylor
    have hnorm : |a N k| * t^k ≤ |H N t| + B k*t^(k+1) + |lower N| := by
      have hh : a N k*t^k = H N t - (H N t-(lower N+a N k*t^k)) - lower N := by ring
      have htri := abs_sub (H N t - (H N t-(lower N+a N k*t^k))) (lower N)
      have htri₂ := abs_sub (H N t) (H N t-(lower N+a N k*t^k))
      rw [← hh, abs_mul, abs_of_nonneg (pow_nonneg htpos.le _)] at htri
      linarith
    have hpow : t^(j+4) ≤ t^(k+1) :=
      pow_le_pow_of_le_one htpos.le htone (by omega)
    have hbound : |a N k| ≤ (C+B k)*t + (err j N + |lower N|)/t^k := by
      apply (mul_le_mul_iff_left₀ (pow_pos htpos k)).mp
      calc
        |a N k| * t^k ≤ |H N t| + B k*t^(k+1) + |lower N| := hnorm
        _ ≤ (C+B k)*t^(k+1) + err j N + |lower N| := by
          have := hsmall j N
          have := mul_le_mul_of_nonneg_left hpow hC
          dsimp [t] at *
          linarith
        _ = ((C+B k)*t + (err j N+|lower N|)/t^k)*t^k := by
          rw [pow_succ]
          field_simp
          ring
    rw [Real.dist_eq, sub_zero]
    exact hbound.trans_lt (by linarith [hN₀ N hN])

end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

/-- Uniform finite Taylor remainders survive an arbitrary probability-space
average. This is a plain Bochner integral statement, not an analyticity axiom. -/
theorem integral_polynomial_remainder {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (F : Z → ℝ) (a : ℕ → Z → ℝ)
    (hF : Integrable F μ) (ha : ∀ j, Integrable (a j) μ) (k : ℕ) (t R : ℝ)
    (hR : ∀ z, |F z - ∑ j ∈ Finset.range (k+1), a j z*t^j| ≤ R) :
    |(∫ z, F z ∂μ) - ∑ j ∈ Finset.range (k+1), (∫ z, a j z ∂μ)*t^j| ≤ R := by
  have hs : Integrable (fun z => ∑ j ∈ Finset.range (k+1), a j z*t^j) μ :=
    integrable_finsetSum _ (fun j _ => (ha j).mul_const _)
  have he : (∫ z, (F z - ∑ j ∈ Finset.range (k+1), a j z*t^j) ∂μ) =
      (∫ z, F z ∂μ) - ∑ j ∈ Finset.range (k+1), (∫ z, a j z ∂μ)*t^j := by
    rw [integral_sub hF hs,integral_finsetSum _ (fun j _ => (ha j).mul_const _)]
    simp_rw [integral_mul_const]
  rw [← he,← Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun z => F z - ∑ j ∈ Finset.range (k+1), a j z*t^j)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hR z))

theorem integral_difference_bound {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (F G : Z → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ) {R : ℝ}
    (hR : ∀ z, |F z-G z| ≤ R) : |(∫ z, F z ∂μ)-(∫ z, G z ∂μ)| ≤ R := by
  rw [← integral_sub hF hG,← Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun z => F z-G z)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hR z))

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundSuperposition
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Set

lemma extractionProbe_le_quarter (j : ℕ) : extractionProbe j ≤ 1/4 := by
  unfold extractionProbe
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+4)]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

lemma extractionProbe_abs_le_quarter (j : ℕ) : |extractionProbe j| ≤ 1/4 := by
  rw [abs_of_pos (extractionProbe_pos j)]
  exact extractionProbe_le_quarter j

lemma probeLow_pos (j : ℕ) : 0 < probeLow j := pow_pos (extractionProbe_pos j) _
lemma probeLow_lt_high (j : ℕ) : probeLow j < probeHigh j := by
  have := probeLow_pos j
  unfold probeHigh
  linarith
lemma probeHigh_lt_quarter (j : ℕ) : probeHigh j < 1/4 := by
  have hp : probeLow j ≤ (1/4:ℝ)^4 := by
    apply (pow_le_pow_left₀ (extractionProbe_pos j).le (extractionProbe_le_quarter j) (j+4)).trans
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold probeHigh
  nlinarith

lemma probe_interval_quarter (j : ℕ) :
    Icc (probeLow j) (probeHigh j) ⊆ Icc (-(1:ℝ)/4) (1/4) := by
  intro u hu
  have := probeLow_pos j
  have := probeHigh_lt_quarter j
  exact ⟨by linarith [hu.1],by linarith [hu.2]⟩

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedError
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_nonneg (z : FullRootState Y X I M) (u center : ℝ) :
    0 ≤ fullSelectedDeviation T Q m base sel fixed D E t z u center :=
  FiniteLaw.expect_nonneg _ (fun _ => abs_nonneg _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) (center : ℝ) :
    fullSelectedDeviation T Q m base sel fixed D E t z u center ≤ 2*(z.2.2.1:ℝ)+|center| := by
  apply (FiniteLaw.expect_mono _ (fun y => (abs_sub _ _).trans
    (add_le_add (KernelTower.perturbScore_bound _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu y) le_rfl))).trans_eq
  exact FiniteLaw.expect_const _ _

theorem measurable_fullSelectedDeviation
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {center : ℝ → ℝ} (hc : Measurable center) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedDeviation T Q m base sel fixed D E t z.1 z.2 (center z.2)) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    fullSelectedDeviation T Q m base sel fixed D E t (h,⟨k,x⟩,⟨n,y⟩) u (center u))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      fullSelectedDeviation T Q m base sel fixed D E t (z.1.1.1,⟨k,z.1.1.2⟩,⟨n,z.2⟩) z.1.2 (center z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    dsimp only [fullSelectedDeviation]
    apply KernelTower.measurable_path_expect L (tower (rootArray n y) L T Q) m
      (f := fun z : (RootPath Y M × RootPath X k) × ℝ =>
        KernelTower.perturbLog (otherLog (base z.1.1 k z.1.2) (rootArray n y) sel fixed)
          (selectedCoefficient (rootArray n y) sel D) (selectedCoefficient (rootArray n y) sel E) t z.2)
      (g := fun z : (RootPath Y M × RootPath X k) × ℝ => fun w =>
        |KernelTower.perturbScore (selectedCoefficient (rootArray n y) sel D)
          (selectedCoefficient (rootArray n y) sel E) t z.2 w-center z.2|)
    · apply KernelTower.measurable_perturbLog
      · intro w
        exact ((hb k (physical (rootArray n y) L w)).comp measurable_fst).add measurable_const
      · exact fun _ _ => measurable_const
      · exact fun _ _ => measurable_const
      · exact measurable_const
      · exact measurable_snd
    · intro w
      exact ((KernelTower.measurable_perturbScore
        (D := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel D)
        (E := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel E)
        (t := fun _ : (RootPath Y M × RootPath X k) × ℝ => t) (u := fun z => z.2)
        (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd w).sub
          (hc.comp measurable_snd)).abs
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterProduct
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory

/-- Selecting one type in the complete dictionary law keeps its unmodified
conditional site law. This is the scalar normalization in the Palm identity. -/
lemma integral_select_product {J Z : Type*} [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace Z] [Countable J] [Countable Z] [MeasurableSingletonClass Z]
    [DecidableEq J] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (j : J) (F : J × Z → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) :
    (∫ x, if x.1 = j then F x else 0 ∂ν.prod τ) =
      ν.real {j} * ∫ z, F (j,z) ∂τ := by
  have hm : Measurable (fun x : J × Z => if x.1 = j then F x else 0) := measurable_of_countable _
  have hi : Integrable (fun x : J × Z => if x.1 = j then F x else 0) (ν.prod τ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; split_ifs; exact hF x; simpa using hB)
  rw [integral_prod _ hi]
  have he : (fun x : J => ∫ z, if x = j then F (x,z) else 0 ∂τ) =
      Set.indicator {j} (fun x => ∫ z, F (x,z) ∂τ) := by
    funext x
    by_cases hx : x = j
    · simp [hx]
    · simp [hx]
  rw [he,integral_indicator (measurableSet_singleton j),integral_singleton]
  rfl

/-- Inserting with a pushed-forward site law is genuinely independent of the
old reservoir. The old state law is not changed by this relabeling. -/
lemma integral_fresh_label {W J Z : Type*} [MeasurableSpace W] [MeasurableSpace J]
    [MeasurableSpace Z] (ρ : Measure W) [IsProbabilityMeasure ρ]
    (τ : Measure Z) [IsProbabilityMeasure τ] (label : Z → J) (hl : Measurable label)
    (F : W × J → ℝ) (hF : Measurable F) {B : ℝ} (hb : ∀ z, |F z| ≤ B) :
    (∫ z, F z ∂ρ.prod (τ.map label)) = ∫ w, ∫ z, F (w,label z) ∂τ ∂ρ := by
  have hi : Integrable F (ρ.prod (τ.map label)) :=
    Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb z))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun w => integral_map hl.aemeasurable (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)

end DilutedSpinGlass
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
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set


lemma boundParameter_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    boundParameter a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeAnchor
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

/-- Every prescribed old leaf has exactly the one-path marginal, including
through shared prefixes and arbitrary (possibly unary) stretches. -/
theorem pathAt_expect {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (T : KernelTower Ω n) (f : FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x)) = (KernelTower.law n T).expect f := by
  induction S with
  | leaf =>
    change KernelTower.unitLaw.expect (fun _ => f ()) = _
    change KernelTower.unitLaw.expect (fun _ => f ()) = KernelTower.unitLaw.expect f
    apply FiniteLaw.expect_congr
    intro x
    cases x
    rfl
  | @node n k C ih =>
    rcases T with ⟨P,Q⟩
    rcases a with ⟨i,a⟩
    change (FiniteLaw.pi (fun i : Fin k => P.bind (fun z => sampleLaw (C i) (Q z)))).expect
      (fun x => f ((x i).1, (C i).pathAt a (x i).2)) = _
    have he := FiniteLaw.expect_pi_marginal
      (fun i : Fin k => P.bind (fun z => sampleLaw (C i) (Q z))) i
      (fun y => f (y.1, (C i).pathAt a y.2))
    refine he.trans ?_
    erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect]
    apply P.expect_congr
    intro z
    exact ih i a (Q z) (fun y => f (z,y))

/-- The anchor-marginal argument in `pert:score-identity`, before root
averaging. It uses the actual old-tree joint law, not independent replicas. -/
theorem anchor_centered_bound {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (T : KernelTower Ω n) (f : Sample Ω S → ℝ) (g : FinitePath Ω n → ℝ)
    {B center : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    |(S.sampleLaw T).expect (fun x => f x * g (S.pathAt a x)) -
      (S.sampleLaw T).expect f * center| ≤
      B * (KernelTower.law n T).expect (fun y => |g y-center|) := by
  have heq : (S.sampleLaw T).expect (fun x => f x * g (S.pathAt a x)) -
      (S.sampleLaw T).expect f * center =
      (S.sampleLaw T).expect (fun x => f x * (g (S.pathAt a x)-center)) := by
    simp only [mul_sub,FiniteLaw.expect_sub,FiniteLaw.expect_mul_right]
  rw [heq]
  have habs : |(S.sampleLaw T).expect (fun x => f x * (g (S.pathAt a x)-center))| ≤
      (S.sampleLaw T).expect (fun x => |f x * (g (S.pathAt a x)-center)|) := by
    apply abs_le.mpr
    constructor
    · have hh := (S.sampleLaw T).expect_mono (fun x => neg_abs_le (f x * (g (S.pathAt a x)-center)))
      simpa only [FiniteLaw.expect_neg] using hh
    · exact (S.sampleLaw T).expect_mono (fun x => le_abs_self _)
  apply habs.trans
  calc
    _ ≤ (S.sampleLaw T).expect (fun x => B * |g (S.pathAt a x)-center|) :=
      FiniteLaw.expect_mono _ (fun x => by
        rw [abs_mul]
        exact mul_le_mul (hf x) le_rfl (abs_nonneg _) hB)
    _ = _ := by
      rw [FiniteLaw.expect_mul_left]
      exact congrArg (fun z => B*z) (pathAt_expect S a T (fun y => |g y-center|))

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
-- module Solutions.OAIQ041_DS.DilutedSpin_SelectedTree
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

variable (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma measurable_fullSelectedTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fullSelectedTreeMean S T Q m base sel fixed D E t u f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only [selectedTreeMean]
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · intro w
    exact (hb k _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_fullSelectedTreeScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fullSelectedTreeScore S a T Q m base sel fixed D E t u f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only [selectedTreeScore]
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · intro w
    exact (hb k _).add measurable_const
  · exact fun _ => measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeMean_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |fullSelectedTreeMean S T Q m base sel fixed D E t u f z| ≤ B :=
  FiniteLaw.abs_expect_le _ (fun _ => hf _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeScore_bound {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) :
    |fullSelectedTreeScore S a T Q m base sel fixed D E t u f z| ≤ 2*B*(z.2.2.1:ℝ) := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul]
  have hscore := KernelTower.perturbScore_bound _ _
    (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu (S.pathAt a x)
  have hb := mul_le_mul (hf (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x))) hscore (abs_nonneg _) hB
  exact hb.trans_eq (by ring)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
/-- Exact old-tree/one-path estimate at every disorder realization, with the
identical selected tower used in the globally centered score error. -/
lemma fullSelectedTree_centered_bound {B center : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (z : FullRootState Y X I M) :
    |fullSelectedTreeScore S a T Q m base sel fixed D E t u f z -
      fullSelectedTreeMean S T Q m base sel fixed D E t u f z * center| ≤
      B * fullSelectedDeviation T Q m base sel fixed D E t z u center := by
  dsimp only [fullSelectedDeviation]
  rw [selected_perturbLog_eq]
  exact PrescribedTree.anchor_centered_bound S a _ _ _ hB (fun x => hf _)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullTreeScore
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
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma integrable_fullSelectedTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    Integrable (fullSelectedTreeMean S T Q m base sel fixed D E t u f) (fullRootLaw ξ μ ν r s) := by
  apply (integrable_const B).mono' (measurable_fullSelectedTreeMean S T Q m base sel fixed D E t u f hb).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using fullSelectedTreeMean_bound S T Q m base sel fixed D E t u f hf z)

lemma integrable_fullSelectedTreeScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    Integrable (fullSelectedTreeScore S a T Q m base sel fixed D E t u f) (fullRootLaw ξ μ ν r s) := by
  have hci := (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  apply (hci.const_mul (2*B)).mono' (measurable_fullSelectedTreeScore S a T Q m base sel fixed D E t u f hb).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using fullSelectedTreeScore_bound S a T Q m base sel fixed D E t u f hB hf hD hE ht hu z)

 
theorem fullTree_score_error
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    |(∫ z, fullSelectedTreeScore S a T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) -
      (∫ z, fullSelectedTreeMean S T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) *
      (∫ z, fullSelectedRawScore T Q m base sel fixed D E t z u ∂fullRootLaw ξ μ ν r s)| ≤
      B * fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u := by
  let P := fullRootLaw ξ μ ν r s
  let center := ∫ z, fullSelectedRawScore T Q m base sel fixed D E t z u ∂P
  have hiM := integrable_fullSelectedTreeMean ξ μ ν r s S T Q m base sel fixed D E t u f hb hf
  have hiS := integrable_fullSelectedTreeScore ξ μ ν r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu
  have hci : Integrable (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) P :=
    (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hiD : Integrable (fun z => fullSelectedDeviation T Q m base sel fixed D E t z u center) P := by
    apply ((hci.const_mul 2).add (integrable_const |center|)).mono'
      ((measurable_fullSelectedDeviation T Q m base sel fixed D E t hb measurable_const).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u center)]
      exact fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  have hh := abs_integral_le_integral_abs.trans (integral_mono
    (hiS.sub (hiM.mul_const center)).abs (hiD.const_mul B)
    (fun z => fullSelectedTree_centered_bound S a T Q m base sel fixed D E t u f hB hf z))
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hiS (hiM.mul_const center),integral_mul_const,integral_const_mul] at hh
  exact hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SelectedPalm
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
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma selectedNumerator_bound (sel : I → Bool)
    (E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hE : ∀ i x y, |E i x y| ≤ 1) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    |selectedNumerator sel E i x y| ≤ 1 := by
  unfold selectedNumerator
  split <;> simp_all

lemma selectedTreeScore_sum (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    selectedTreeScore S a T Q m base roots sel fixed D E t u f =
      ∑ q, treeScore S a T Q m base roots (selectedFactor sel fixed D E t u)
        (selectedNumerator sel E) f q := by
  simp only [selectedTreeScore,KernelTower.perturbScore,Finset.mul_sum,treeScore,
    ← FiniteLaw.expect_sum]
  apply FiniteLaw.expect_congr
  intro x
  apply Finset.sum_congr rfl
  intro q _
  cases h : sel (roots q) <;> simp [selectedCoefficient,selectedFactor,selectedNumerator,h]

lemma selectedTreeScore_one (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    selectedTreeScore S a T Q m base roots sel fixed D E t u (fun _ => 1) =
      selectedScore T Q m base roots sel fixed D E t u := by
  simp only [selectedTreeScore,one_mul,selectedScore]
  exact PrescribedTree.pathAt_expect S a _ _

variable [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

/-- Selected score Palm at a fixed physical realization. The whole original
root-label reservoir is retained; only one independent label/mark is inserted. -/
theorem selected_palm (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ n : ℕ, ∫ y, selectedTreeScore S a T Q m base (rootArray n y) sel fixed D E t u f
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s) =
      (s:ℝ) * ∫ n : ℕ, ∫ i, ∫ y,
        insertedTreeScore S a T Q m base (rootArray n y) i
          (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
        ∂rootLaw n (fun _ => ν) ∂ν ∂poissonMeasure s := by
  have heL (n : ℕ) := integral_rootArray_eq_pi ν n
    (fun roots => selectedTreeScore S a T Q m base roots sel fixed D E t u f)
  have heR (n : ℕ) (i : I) := integral_rootArray_eq_pi ν n
    (fun roots => insertedTreeScore S a T Q m base roots i
      (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f)
  simp_rw [heL,heR,selectedTreeScore_sum]
  exact full_reservoir_palm ν S a s T Q m base _ _ f hf (selectedNumerator_bound sel E hE) hA

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullPalm
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

lemma measurable_treeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin n)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => treeScore S a T Q m (base z) roots factor numerator f q) := by
  unfold treeScore
  refine PrescribedTree.measurable_tilt_sample_expect S (tower roots L T Q) m ?_ ?_
  · exact fun w => (hb _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_selectedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => selectedTreeScore S a T Q m (base z) roots sel fixed D E t u f) := by
  unfold selectedTreeScore
  refine PrescribedTree.measurable_tilt_sample_expect S (tower roots L T Q) m ?_ ?_
  · exact fun w => (hb _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_insertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => insertedTreeScore S a T Q m (base z) roots i factor numerator f) := by
  simpa only [treeScore_insertion] using measurable_treeScore S a T Q m base (Fin.cons i roots) factor numerator f 0 hb

lemma abs_insertedTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i x y, |numerator i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ factor i x y) :
    |insertedTreeScore S a T Q m base roots i factor numerator f| ≤ 2*B := by
  rw [← treeScore_insertion]
  exact abs_treeScore_le S a T Q m base _ factor numerator f 0 hf hn hA

variable [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
lemma measurable_averagedInsertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => averagedInsertedTreeScore ν S a T Q m (base z) roots factor numerator f) := by
  have hh : Measurable (fun z : Z × I => insertedTreeScore S a T Q m (base z.1) roots z.2 factor numerator f) := by
    apply measurable_from_prod_countable_left
    exact fun i => measurable_insertedTreeScore S a T Q m base roots i factor numerator f hb
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

omit [Countable I] [MeasurableSingletonClass I] in
lemma abs_averagedInsertedTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i x y, |numerator i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ factor i x y) :
    |averagedInsertedTreeScore ν S a T Q m base roots factor numerator f| ≤ 2*B := by
  have hh := norm_integral_le_of_norm_le_const (μ := ν) (C := 2*B)
    (f := fun i => insertedTreeScore S a T Q m base roots i factor numerator f)
    (ae_of_all _ (fun i => by simpa only [Real.norm_eq_abs] using abs_insertedTreeScore_le S a T Q m base roots i factor numerator f hf hn hA))
  simpa only [averagedInsertedTreeScore,Real.norm_eq_abs,probReal_univ,mul_one] using hh

end DilutedSpinGlass.HeterogeneousMarks
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

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootTreeMean_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |rootTreeMean S T Q m base old f z| ≤ B :=
  FiniteLaw.abs_expect_le _ (fun _ => hf _)

omit [Countable I] [MeasurableSingletonClass I] in
lemma oldTreeAverage_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |oldTreeAverage ξ μ ν r s S T Q m base old f| ≤ B := by
  simpa only [oldTreeAverage, Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := fullRootLaw ξ μ ν r s)
      (f := rootTreeMean S T Q m base old f)
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using rootTreeMean_bound S T Q m base old f hf z))

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I J X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma selectedParameterFactor_eq (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (j : J) (u : J → ℝ) :
    selectedFactor (fun i => decide (key i = j)) (parameterFactor key a b t D E u)
      D E (t j) (boundParameter (a j) (b j) (u j)) = parameterFactor key a b t D E u := by
  funext i x y
  by_cases h : key i = j <;> simp [selectedFactor,parameterFactor,h]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
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
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

lemma inserted_eq_external (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    insertedTreeScore S a T Q m base roots i factor numerator f =
      externalTreeScore S a T Q m base roots i factor (factor i) (numerator i) f := rfl

/-- Exact link to the proved all-order anchor Taylor calculus, for arbitrary
old disorder and mark alphabets; the old kernels do not vary with `new`. -/
lemma external_eq_anchorInsertion (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new numerator : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    externalTreeScore S a T Q (fun j => m j.succ) base roots i old new numerator f =
      PrescribedTree.anchorInsertion S
        (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) (fun j => m j.succ)
          (logWeight base roots old)) (markPrior L (Q i))) m a
        (fun x => f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
          numerator (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
            (KernelTower.pathSnd L (S.pathAt a x)))
        (fun y => new (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)) := by
  apply FiniteLaw.expect_congr
  intro x
  exact (mul_div_assoc _ _ _).symm

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

lemma measurable_externalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => externalTreeScore S a T Q m (base z) roots i old new E f) := by
  unfold externalTreeScore
  simp_rw [← KernelTower.tilt_prod_fst,KernelTower.tilt_insertion]
  refine PrescribedTree.measurable_tilt_sample_expect S
    (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) m ?_ ?_
  · exact fun y => ((hb _).add measurable_const).add measurable_const
  · exact fun x => measurable_const

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

lemma abs_externalTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ x y, |E x y| ≤ 1) (hA : ∀ x y, 1/2 ≤ new x y) :
    |externalTreeScore S a T Q m base roots i old new E f| ≤ 2*B := by
  apply FiniteLaw.abs_expect_le
  intro x
  let xa := physical roots L (KernelTower.pathFst L (S.pathAt a x))
  let ya := KernelTower.pathSnd L (S.pathAt a x)
  have hp : 0 < new xa ya := lt_of_lt_of_le (by norm_num) (hA xa ya)
  change |f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) * (E xa ya/new xa ya)| ≤ 2*B
  rw [abs_mul,abs_div,abs_of_pos hp]
  have hq : |E xa ya| / new xa ya ≤ 2 := by
    apply (div_le_iff₀ hp).mpr
    linarith [hE xa ya,hA xa ya]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))))
  calc
    _ ≤ B*2 := mul_le_mul (hf _) hq (div_nonneg (abs_nonneg _) hp.le) hB
    _ = 2*B := mul_comm _ _

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

include hm hmono hpos hroot hend hB hf hD hE in
 
lemma externalTreeScore_sub_le {t u : ℝ} (ht : |t| ≤ 1/4) (huz : 0 ≤ u) (hu : u ≤ 1/4) :
    |externalTreeScore S a T Q (fun j => m j.succ) base roots i old
        (fun x y => 1+t*D x y+u*E x y) E f -
      externalTreeScore S a T Q (fun j => m j.succ) base roots i old
        (fun x y => 1+t*D x y) E f| ≤ (4+8*(S.leaves:ℝ))*B*u := by
  rw [external_eq_anchorInsertion,external_eq_anchorInsertion]
  apply PrescribedTree.anchorInsertion_sub_le S _ m hm hmono hpos hroot hend a _ _ _ hB
  · intro x
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (hf _) (hE _ _) (abs_nonneg _) hB
  · exact fun y => hD _ _
  · exact fun y => hE _ _
  · exact ht
  · exact huz
  · exact hu

include hm hmono hpos hroot hend hB hf hD hE in
lemma externalTreeScore_taylor_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (1/2)) (k : ℕ) :
    |externalTreeScore S a T Q (fun j => m j.succ) base roots i old
        (fun x y => 1+t*D x y) E f -
      ∑ j ∈ Finset.range (k+1), externalCoefficient S a T Q m base roots i old D E f j*t^j| ≤
        (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1) := by
  rw [external_eq_anchorInsertion]
  apply PrescribedTree.anchorInsertion_taylor_bound S _ m hm hmono hpos hroot hend _ (fun y => hD _ _) a _ hB
  · intro x
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (hf _) (hE _ _) (abs_nonneg _) hB
  · exact ht

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRootPalm
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
    (ν : Measure I) [IsProbabilityMeasure ν]

lemma selected_palm_averaged (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ n : ℕ, ∫ y, selectedTreeScore S a T Q m base (rootArray n y) sel fixed D E t u f
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s) =
      (s:ℝ) * ∫ n : ℕ, ∫ y,
        averagedInsertedTreeScore ν S a T Q m base (rootArray n y)
          (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s := by
  rw [selected_palm ν S a s T Q m base sel fixed D E t u f hf hE hA]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro n
  apply integral_integral_swap
  exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (2*B)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.uncurry] using
      abs_insertedTreeScore_le S a T Q m base (rootArray n z.2) z.1 _ _ f hf (selectedNumerator_bound sel E hE) hA))

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- Full-root Palm identity, including the original physical Poisson/sample
and field laws. The surviving root law on the right is exactly the left law. -/
theorem fullRoot_selected_palm
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ z, fullSelectedTreeScore S a T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) =
      (s:ℝ) * ∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f z ∂fullRootLaw ξ μ ν r s := by
  let F := fun h k x n y => selectedTreeScore S a T Q m (base h k x) (rootArray n y) sel fixed D E t u f
  let G := fun h k x n y => averagedInsertedTreeScore ν S a T Q m (base h k x) (rootArray n y)
    (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_selectedTreeScore S a T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) sel fixed D E t u f (hb k)
  have hG (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => G z.1.1 k z.1.2 n z.2) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_averagedInsertedTreeScore ν S a T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) _ _ f (hb k)
  have hFb (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |F h k x n y| ≤ 2*B+0*(k:ℝ)^2+2*B*(n:ℝ)^2 := by
    have hh := fullSelectedTreeScore_bound S a T Q m base sel fixed D E t u f hB hf hD hE ht hu (h,⟨k,x⟩,⟨n,y⟩)
    have hn : (n:ℝ) ≤ 1+(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-1), (show 0 ≤ (n:ℝ) by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*B by positivity)
    dsimp only [fullSelectedTreeScore,packRoot] at hh
    dsimp only [F]
    nlinarith
  have hGb (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |G h k x n y| ≤ 2*B+0*(k:ℝ)^2+0*(n:ℝ)^2 := by
    simpa only [zero_mul,add_zero] using abs_averagedInsertedTreeScore_le ν S a T Q m (base h k x) (rootArray n y) _ _ f hf (selectedNumerator_bound sel E hE) hA
  change (∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s) = (s:ℝ) * ∫ z, packRoot G z ∂fullRootLaw ξ μ ν r s
  rw [integral_fullRootLaw_quadratic ξ μ ν r s hF hFb,
    integral_fullRootLaw_quadratic ξ μ ν r s hG hGb]
  dsimp only [F,G]
  simp_rw [selected_palm_averaged ν S a s T Q m _ sel fixed D E t u f hf hE hA,
    integral_const_mul]

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

lemma measurable_rootExternalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old new E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × I => rootExternalTreeScore S a T Q m base old new E f z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro i
  dsimp only [rootExternalTreeScore]
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  exact measurable_externalTreeScore S a T Q m
    (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) i old (new i) (E i) f (hb k)

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

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν η : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

variable (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)

include hE hf hb in
lemma integrable_rootExternalTreeScore (new : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hA : ∀ i x y, 1/2 ≤ new i x y) :
    Integrable (fun z : FullRootState Y X I M × I =>
      rootExternalTreeScore S a T Q (fun j => m j.succ) base old new E f z.1 z.2)
      ((fullRootLaw ξ μ ν r s).prod η) := by
  apply Integrable.of_bound (measurable_rootExternalTreeScore S a T Q _ base old new E f hb).aestronglyMeasurable (2*B)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact abs_externalTreeScore_le S a T Q _ (base z.1.1 z.1.2.1.1 z.1.2.1.2)
      (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (new z.2) (E z.2) f hf (hE z.2) (hA z.2))

include hmono hpos hroot hend hB hf hD hE hb hm in
lemma integrable_rootExternalCoefficient (j : ℕ) :
    Integrable (fun z : FullRootState Y X I M × I => rootExternalCoefficient S a T Q m base old D E f j z.1 z.2)
      ((fullRootLaw ξ μ ν r s).prod η) := by
  apply Integrable.of_bound (measurable_rootExternalCoefficient S a T Q m hm base old D E f j hb).aestronglyMeasurable
    (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) j/(j.factorial:ℝ))
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact externalCoefficient_bound S a T Q m hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (D z.2) (E z.2) f hB hf (hD z.2) (hE z.2) j)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalAverageTaylor
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
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν η : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)

lemma affine_one_lower {d t : ℝ} (hd : |d| ≤ 1) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) :
    1/2 ≤ 1+t*d := by
  have hd0 := (abs_le.mp hd).1
  rcases ht with ⟨ht0,ht1⟩
  nlinarith [mul_nonneg ht0 (show 0 ≤ d+1 by linarith)]

lemma affine_two_lower {d e t u : ℝ} (hd : |d| ≤ 1) (he : |e| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) : 1/2 ≤ 1+t*d+u*e := by
  have htd : |t*d| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg t,abs_nonneg d]
  have hue : |u*e| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg u,abs_nonneg e]
  linarith [(abs_le.mp htd).1,(abs_le.mp hue).1]

include hb hm hmono hpos hroot hend hB hf hD hE in
/-- Full finite-volume disorder averaging of the uniform all-order Taylor
bound. Physical fields, physical Poisson terms and the entire countable
reservoir are unchanged as the new insertion parameter varies. -/
theorem externalAverage_taylor_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (1/2)) (k : ℕ) :
    |externalAverage ξ μ ν η r s S a T Q m base old D E f t 0 -
      ∑ j ∈ Finset.range (k+1), externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E f j*t^j| ≤
        (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1) := by
  unfold externalAverage externalCoefficientAverage
  simp only [zero_mul, add_zero]
  apply integral_polynomial_remainder
  · exact integrable_rootExternalTreeScore ξ μ ν η r s S a T Q m base old E f hb hf hE _
      (fun i x y => affine_one_lower (hD i x y) ht)
  · intro j
    exact integrable_rootExternalCoefficient ξ μ ν η r s S a T Q m base old D E f hb hm hmono hpos hroot hend hB hf hD hE j
  · intro z
    exact externalTreeScore_taylor_bound S a T Q m hm hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (D z.2) (E z.2) f hB hf (hD z.2) (hE z.2) ht k

include hb hm hmono hpos hroot hend hB hf hD hE in
theorem externalAverage_sub_le {t u : ℝ} (ht : |t| ≤ 1/4) (huz : 0 ≤ u) (hu : u ≤ 1/4) :
    |externalAverage ξ μ ν η r s S a T Q m base old D E f t u -
      externalAverage ξ μ ν η r s S a T Q m base old D E f t 0| ≤ (4+8*(S.leaves:ℝ))*B*u := by
  unfold externalAverage
  simp only [zero_mul, add_zero]
  apply integral_difference_bound
  · exact integrable_rootExternalTreeScore ξ μ ν η r s S a T Q m base old E f hb hf hE _
      (fun i x y => affine_two_lower (hD i x y) (hE i x y) ht (by rwa [abs_of_nonneg huz]))
  · exact integrable_rootExternalTreeScore ξ μ ν η r s S a T Q m base old E f hb hf hE _
      (fun i x y => by simpa only [zero_mul,add_zero] using affine_two_lower (hD i x y) (hE i x y) ht (show |(0:ℝ)| ≤ 1/4 by norm_num))
  · intro z
    exact externalTreeScore_sub_le S a T Q m hm hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (D z.2) (E z.2) f hB hf (hD z.2) (hE z.2) ht huz hu

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalCovariance
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
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν η : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)


variable (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)

include hb hm hmono hpos hroot hend hB hf hD hE in
lemma externalCovariance_taylor_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (1/2)) (k : ℕ) :
    |externalCovariance ξ μ ν η r s S a T Q m base old D E f t 0 -
      ∑ j ∈ Finset.range (k+1), covarianceCoefficient ξ μ ν η r s S a T Q m base old D E f j*t^j| ≤
        (2*B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1) := by
  have h1 := externalAverage_taylor_bound ξ μ ν η r s S a T Q m base old D E f hb hm hmono hpos hroot hend hB hf hD hE ht k
  have h2 := externalAverage_taylor_bound ξ μ ν η r s S a T Q m base old D E (fun _ => 1) hb hm hmono hpos hroot hend
    (by norm_num : (0:ℝ) ≤ 1) (by intro _; norm_num) hD hE ht k
  have hmean := oldTreeAverage_bound ξ μ ν r s S T Q (fun j => m j.succ) base old f hf
  let c := oldTreeAverage ξ μ ν r s S T Q (fun j => m j.succ) base old f
  let F := externalAverage ξ μ ν η r s S a T Q m base old D E f t 0
  let G := externalAverage ξ μ ν η r s S a T Q m base old D E (fun _ => 1) t 0
  let P := ∑ j ∈ Finset.range (k+1), externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E f j*t^j
  let R := ∑ j ∈ Finset.range (k+1), externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E (fun _ => 1) j*t^j
  have he : externalCovariance ξ μ ν η r s S a T Q m base old D E f t 0 -
      ∑ j ∈ Finset.range (k+1), covarianceCoefficient ξ μ ν η r s S a T Q m base old D E f j*t^j = (F-P)-c*(G-R) := by
    simp only [externalCovariance,covarianceCoefficient,sub_mul,Finset.sum_sub_distrib,mul_assoc,← Finset.mul_sum]
    dsimp only [F,P,c,G,R]
    ring
  rw [he]
  have hh := (abs_sub (F-P) (c*(G-R))).trans (add_le_add h1 (show |c*(G-R)| ≤ B*((1*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1)) from by
    rw [abs_mul]
    exact mul_le_mul hmean h2 (abs_nonneg _) hB))
  calc
    _ ≤ (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1) +
        B*((1*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) (k+1)/(k.factorial:ℝ))*t^(k+1)) := hh
    _ = _ := by ring

include hb hm hmono hpos hroot hend hB hf hD hE in
lemma externalCovariance_sub_le {t u : ℝ} (ht : |t| ≤ 1/4) (huz : 0 ≤ u) (hu : u ≤ 1/4) :
    |externalCovariance ξ μ ν η r s S a T Q m base old D E f t u -
      externalCovariance ξ μ ν η r s S a T Q m base old D E f t 0| ≤ 2*(4+8*(S.leaves:ℝ))*B*u := by
  have h1 := externalAverage_sub_le ξ μ ν η r s S a T Q m base old D E f hb hm hmono hpos hroot hend hB hf hD hE ht huz hu
  have h2 := externalAverage_sub_le ξ μ ν η r s S a T Q m base old D E (fun _ => 1) hb hm hmono hpos hroot hend
    (by norm_num : (0:ℝ) ≤ 1) (by intro _; norm_num) hD hE ht huz hu
  have hmean := oldTreeAverage_bound ξ μ ν r s S T Q (fun j => m j.succ) base old f hf
  unfold externalCovariance
  rw [show ∀ F G F' G' c : ℝ, (F-c*G)-(F'-c*G')=(F-F')-c*(G-G') by intros; ring]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have hh := mul_le_mul hmean h2 (abs_nonneg _) hB
  linarith

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalFreshLaw
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

lemma externalAverage_fresh_label
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i x y, |E i x y| ≤ 1) (t u : ℝ)
    (hA : ∀ i x y, 1/2 ≤ 1+t*D i x y+u*E i x y)
    (label : Z → I) (hl : Measurable label) :
    externalAverage ξ μ ν (τ.map label) r s S a T Q m base old D E f t u =
      ∫ z, ∫ q, rootExternalTreeScore S a T Q (fun l => m l.succ) base old
        (fun i x y => 1+t*D i x y+u*E i x y) E f z (label q) ∂τ ∂fullRootLaw ξ μ ν r s := by
  apply integral_fresh_label (fullRootLaw ξ μ ν r s) τ label hl
  · exact measurable_rootExternalTreeScore S a T Q _ base old _ E f hb
  · intro z
    exact abs_externalTreeScore_le S a T Q _ (base z.1.1 z.1.2.1.1 z.1.2.1.2)
      (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old _ _ f hf (hE z.2) (hA z.2)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CommonFresh
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
variable {Ω K Z X Y : Type} [Fintype Ω]
    [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : K → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure ((K × ℕ) × Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : K) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : (K × ℕ) × Z) → FinitePath Ω L → FinitePath (A i.1.1) L → ℝ)
    (D E : (i : K) → Z → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
  [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [MeasurableSpace X] [MeasurableSpace Y] in
/-- Changing only the fresh probe label does not change its alphabet, prior,
or observable. All old labels, factors, and counts remain literally fixed. -/
lemma rootExternalTreeScore_probe (q : K) (j k : ℕ) (z : FullRootState Y X ((K×ℕ)×Z) M)
    (v : Z) (t u : ℝ) :
    rootExternalTreeScore S a T (fun i => Q i.1.1) (fun l => m l.succ) base old
      (fun i x y => 1+t*D i.1.1 i.2 x y+u*E i.1.1 i.2 x y)
      (fun i => E i.1.1 i.2) f z ((q,j),v) =
    rootExternalTreeScore S a T (fun i => Q i.1.1) (fun l => m l.succ) base old
      (fun i x y => 1+t*D i.1.1 i.2 x y+u*E i.1.1 i.2 x y)
      (fun i => E i.1.1 i.2) f z ((q,k),v) := rfl

lemma externalAverage_probe
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i v x y, |E i v x y| ≤ 1) (t u : ℝ)
    (hA : ∀ i v x y, 1/2 ≤ 1+t*D i v x y+u*E i v x y) (q : K) (j k : ℕ) :
    externalAverage ξ μ ν (τ.map (fun v => ((q,j),v))) r s S a T (fun i => Q i.1.1) m base old
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f t u =
    externalAverage ξ μ ν (τ.map (fun v => ((q,k),v))) r s S a T (fun i => Q i.1.1) m base old
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f t u := by
  rw [externalAverage_fresh_label ξ μ ν τ r s S a T (fun i => Q i.1.1) m base old
        (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f hb hf (fun i => hE i.1.1 i.2) t u
        (fun i => hA i.1.1 i.2) (fun v : Z => ((q,j),v)) (measurable_const.prodMk measurable_id),
    externalAverage_fresh_label ξ μ ν τ r s S a T (fun i => Q i.1.1) m base old
        (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f hb hf (fun i => hE i.1.1 i.2) t u
        (fun i => hA i.1.1 i.2) (fun v : Z => ((q,k),v)) (measurable_const.prodMk measurable_id)]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with v
  exact rootExternalTreeScore_probe S a T Q m base old D E f q j k z v t u

lemma externalCovariance_probe
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i v x y, |E i v x y| ≤ 1) (t u : ℝ)
    (hA : ∀ i v x y, 1/2 ≤ 1+t*D i v x y+u*E i v x y) (q : K) (j k : ℕ) :
    externalCovariance ξ μ ν (τ.map (fun v => ((q,j),v))) r s S a T (fun i => Q i.1.1) m base old
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f t u =
    externalCovariance ξ μ ν (τ.map (fun v => ((q,k),v))) r s S a T (fun i => Q i.1.1) m base old
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f t u := by
  unfold externalCovariance
  rw [externalAverage_probe ξ μ ν τ r s S a T Q m base old D E f hb hf hE t u hA q j k,
    externalAverage_probe ξ μ ν τ r s S a T Q m base old D E (fun _ => 1) hb
      (B := 1) (by intro; norm_num) hE t u hA q j k]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PalmError
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
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma fullSelectedTreeScore_one (z : FullRootState Y X I M) :
    fullSelectedTreeScore S a T Q m base sel fixed D E t u (fun _ => 1) z =
      fullSelectedRawScore T Q m base sel fixed D E t z u := by
  exact selectedTreeScore_one S a T Q m (base z.1 z.2.1.1 z.2.1.2)
    (rootArray z.2.2.1 z.2.2.2) sel fixed D E t u

/-- The Palm covariance bound under the same complete original reservoir.
Normalization by a type mass `c` can be done after this identity; no root
Poisson families have been deleted or resampled. -/
theorem fullRoot_palm_error
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) (hs : 0 < s) :
    |(∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f z ∂fullRootLaw ξ μ ν r s) -
      (∫ z, fullSelectedTreeMean S T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) *
      (∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) (fun _ => 1) z ∂fullRootLaw ξ μ ν r s)| ≤
      B * fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u / (s:ℝ) := by
  have hh := fullTree_score_error ξ μ ν r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu
  rw [fullRoot_selected_palm ν ξ μ r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu hA] at hh
  have hone := fullRoot_selected_palm ν ξ μ r s S a T Q m base sel fixed D E t u (fun _ => 1)
    hb (by norm_num : (0:ℝ) ≤ 1) (by intro x; norm_num : ∀ x, |(1:ℝ)| ≤ 1) hD hE ht hu hA
  simp_rw [fullSelectedTreeScore_one] at hone
  rw [hone] at hh
  have hsr : (0:ℝ) < s := by exact_mod_cast hs
  rw [mul_left_comm _ (s:ℝ), ← mul_sub,abs_mul,abs_of_pos hsr] at hh
  exact (le_div_iff₀ hsr).mpr (by nlinarith)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DictionaryPalm
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
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

lemma insertedTreeScore_selected (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    insertedTreeScore S a T Q m base roots i (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f =
      if sel i then externalTreeScore S a T Q m base roots i (selectedFactor sel fixed D E t u)
        (fun x y => 1+t*D i x y+u*E i x y) (E i) f else 0 := by
  rw [inserted_eq_external]
  cases hi : sel i
  · have hn : selectedNumerator sel E i = fun _ _ => 0 := by funext x y; simp only [selectedNumerator,hi,Bool.false_eq_true,ite_false]
    rw [hn]
    simp only [externalTreeScore,zero_div,mul_zero,FiniteLaw.expect_const,Bool.false_eq_true,ite_false]
  · have hn : selectedNumerator sel E i = E i := by funext x y; simp only [selectedNumerator,hi,ite_true]
    have ha : selectedFactor sel fixed D E t u i = fun x y => 1+t*D i x y+u*E i x y := by
      funext x y
      simp only [selectedFactor,hi,ite_true]
    rw [hn,ha]
    simp only [ite_true]

variable {J Z X Y : Type} [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {M : ℕ}
    {C : J × Z → Type} [∀ i, Fintype (C i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (C i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (fixed D E : (i : J × Z) → FinitePath Ω L → FinitePath (C i) L → ℝ)
    (j : J) (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- The exact mass of a selected type emerges from the full law, with its
site average independent of the unchanged complete reservoir. -/
lemma fullInserted_select_type
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ 1+t*D i x y+u*E i x y) :
    (∫ z, fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base
      (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u)
      (selectedNumerator (fun i => decide (i.1 = j)) E) f z ∂fullRootLaw ξ μ (ν.prod τ) r s) =
      ν.real {j} * externalAverage ξ μ (ν.prod τ) (τ.map (fun z => (j,z))) r s S a T Q m base
        (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) D E f t u := by
  let old := selectedFactor (fun i : J × Z => decide (i.1 = j)) fixed D E t u
  let F : FullRootState Y X (J × Z) M × (J × Z) → ℝ := fun z =>
    rootExternalTreeScore S a T Q (fun l => m l.succ) base old
      (fun i x y => 1+t*D i x y+u*E i x y) E f z.1 z.2
  have hFm : Measurable F := measurable_rootExternalTreeScore S a T Q _ base old _ E f hb
  have hFb (z) : |F z| ≤ 2*B :=
    abs_externalTreeScore_le S a T Q _ (base z.1.1 z.1.2.1.1 z.1.2.1.2)
      (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old _ _ f hf (hE z.2) (hA z.2)
  have he (z : FullRootState Y X (J × Z) M) :
      fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base old
        (selectedNumerator (fun i => decide (i.1 = j)) E) f z =
        ν.real {j} * ∫ q, F (z,(j,q)) ∂τ := by
    dsimp only [fullInsertedTreeScore,packRoot,averagedInsertedTreeScore,old]
    simp_rw [insertedTreeScore_selected]
    simpa only [decide_eq_true_eq,F,rootExternalTreeScore,packRoot,old] using
      integral_select_product ν τ j (fun i => F (z,i)) (by positivity) (fun i => hFb (z,i))
  change (∫ z, fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base old
    (selectedNumerator (fun i => decide (i.1 = j)) E) f z ∂fullRootLaw ξ μ (ν.prod τ) r s) = _
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  unfold externalAverage
  exact (integral_fresh_label (fullRootLaw ξ μ (ν.prod τ) r s) τ (fun q => (j,q))
    (measurable_const.prodMk measurable_id) F hFm hFb).symm

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_NormalizedPalm
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
variable {Ω J Z X Y : Type} [Fintype Ω]
    [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : J × Z → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (fixed D E : (i : J × Z) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

 
theorem normalized_dictionary_palm
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor (fun i => decide (i.1 = j)) fixed D E t u i x y)
    (hc : 0 < ν.real {j}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun q => (j,q))) r s S a T Q m base
      (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) D E f t u| ≤
      B * fullSelectedError ξ μ (ν.prod τ) r s T Q (fun l => m l.succ) base
        (fun i => decide (i.1 = j)) fixed D E t u / (ν.real {j}*(s:ℝ)) := by
  have haff (i x y) : 1/2 ≤ 1+t*D i x y+u*E i x y := by
    have hd := mul_le_mul ht (hD i x y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
    have he := mul_le_mul hu (hE i x y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
    rw [← abs_mul] at hd he
    linarith [(abs_le.mp hd).1,(abs_le.mp he).1]
  have hh := fullRoot_palm_error ξ μ (ν.prod τ) r s S a T Q (fun l => m l.succ) base
    (fun i => decide (i.1 = j)) fixed D E t u f hb hB hf hD hE ht hu hA hs
  rw [fullInserted_select_type ξ μ ν τ r s S a T Q m base fixed D E j t u f hb hB hf hE haff,
    fullInserted_select_type ξ μ ν τ r s S a T Q m base fixed D E j t u (fun _ => 1) hb
      (by norm_num : (0:ℝ) ≤ 1) (by intro _; norm_num) hE haff] at hh
  change |ν.real {j} * _ - oldTreeAverage ξ μ (ν.prod τ) r s S T Q (fun l => m l.succ) base
    (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) f * (ν.real {j} * _)| ≤ _ at hh
  rw [mul_left_comm _ (ν.real {j}), ← mul_sub,abs_mul,abs_of_pos hc] at hh
  unfold externalCovariance
  have hh' := (le_div_iff₀ hc).mpr (by simpa only [mul_comm (ν.real {j})] using hh)
  simpa only [div_div, mul_comm (s:ℝ)] using hh'

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterPalm
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
variable {Ω J Z X Y : Type} [Fintype Ω]
    [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : J × Z → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (a b t : J → ℝ) (D E : (i : J × Z) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (u : J → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- Actual parameter-score Palm inequality: all old factors are the literal
full dictionary factors at u, including the selected type. -/
theorem parameter_dictionary_palm
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
    (ht : ∀ j, |t j| ≤ 1/4)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hc : 0 < ν.real {j}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun q => (j,q))) r s S anchor T Q m base
      (parameterFactor Prod.fst a b t D E u) D E f (t j) (boundParameter (a j) (b j) (u j))| ≤
      B * (parameterError ξ μ (ν.prod τ) r s T Q (fun l => m l.succ) base
        Prod.fst a b t D E j u / (ν.real {j}*(s:ℝ))) := by
  have hu (j : J) : |boundParameter (a j) (b j) (u j)| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI j (boundParameter_mem (hab j) (u j))).1],
      (hI j (boundParameter_mem (hab j) (u j))).2⟩
  have hA (i : J × Z) (x y) : 1/2 ≤ parameterFactor Prod.fst a b t D E u i x y :=
    affine_two_lower (hD i x y) (hE i x y) (ht i.1) (hu i.1)
  have he := selectedParameterFactor_eq Prod.fst a b t D E j u
  have hh := normalized_dictionary_palm ξ μ ν τ r s S anchor T Q m base
    (parameterFactor Prod.fst a b t D E u) D E j (t j) (boundParameter (a j) (b j) (u j)) f
    hb hB hf hD hE (ht j) (hu j) (by rw [he]; exact hA) hc hs
  rw [he] at hh
  simpa only [parameterError,mul_div_assoc] using hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DictionaryAnalytic
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
variable {Ω K Z X Y : Type} [Fintype Ω]
    [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : K → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : K) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (D E : (i : K) → Z → FinitePath Ω L → FinitePath (A i) L → ℝ)

/-- A single old-reservoir analytic function is small at every prescribed probe.
The trace j occurs only in the independently inserted mark; it is not erased
from or changed inside the old ambient Poisson dictionary. -/
theorem dictionary_covariance_probe_bound
    (u : K×ℕ → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : K) (j : ℕ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i v x y, |D i v x y| ≤ 1) (hE : ∀ i v x y, |E i v x y| ≤ 1)
    (hc : 0 < ν.real {(q,j)}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun v => ((q,0),v))) r s S anchor T
      (fun i => Q i.1.1) m base (dictionaryFactor D E u)
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f (extractionProbe j) 0| ≤
      4*(4+8*(S.leaves:ℝ))*B*extractionProbe j^(j+4) +
      B*(parameterError ξ μ (ν.prod τ) r s T (fun i => Q i.1.1) (fun l => m l.succ) base
        Prod.fst (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
        (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) (q,j) u / (ν.real {(q,j)}*(s:ℝ))) := by
  let v := boundParameter (probeLow j) (probeHigh j) (u (q,j))
  have hv := boundParameter_mem (probeLow_lt_high j).le (u (q,j))
  have hv0 : 0 ≤ v := (probeLow_pos j).le.trans hv.1
  have hv1 : v ≤ 1/4 := hv.2.trans (probeHigh_lt_quarter j).le
  have hp := parameter_dictionary_palm ξ μ ν τ r s S anchor T (fun i => Q i.1.1) m base
    (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
    (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) (q,j) u f hb hB hf
    (fun i => (probeLow_lt_high i.2).le) (fun i => probe_interval_quarter i.2)
    (fun i => extractionProbe_abs_le_quarter i.2) (fun i => hD i.1.1 i.2)
    (fun i => hE i.1.1 i.2) hc hs
  haveI : IsProbabilityMeasure (τ.map (fun v => ((q,j),v))) := Measure.isProbabilityMeasure_map (by fun_prop)
  have hl := externalCovariance_sub_le ξ μ (ν.prod τ) (τ.map (fun v => ((q,j),v))) r s S anchor T
    (fun i => Q i.1.1) m base (dictionaryFactor D E u)
    (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f hb hm hmono hpos hroot hend hB hf
    (fun i => hD i.1.1 i.2) (fun i => hE i.1.1 i.2) (extractionProbe_abs_le_quarter j) hv0 hv1
  have hA (i : K) (v : Z) (x y) : 1/2 ≤ 1+extractionProbe j*D i v x y+0*E i v x y :=
    affine_two_lower (hD i v x y) (hE i v x y) (extractionProbe_abs_le_quarter j) (by norm_num)
  rw [externalCovariance_probe ξ μ (ν.prod τ) τ r s S anchor T Q m base (dictionaryFactor D E u)
    D E f hb hf hE (extractionProbe j) 0
    hA q 0 j]
  have hcoef : 0 ≤ 2*(4+8*(S.leaves:ℝ))*B := by positivity
  have hl' := hl.trans (mul_le_mul_of_nonneg_left hv.2 hcoef)
  dsimp only [dictionaryFactor] at hl'
  -- |H(0)| ≤ |H(v)| + |H(v)-H(0)|, with the two estimates proved above.
  have htri (x y : ℝ) : |y| ≤ |x|+|x-y| := by
    have := abs_sub x (x-y)
    rw [show x-(x-y)=y by ring] at this
    exact this
  have hh := htri
    (externalCovariance ξ μ (ν.prod τ) (τ.map (fun v => ((q,j),v))) r s S anchor T
      (fun i => Q i.1.1) m base (dictionaryFactor D E u)
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f (extractionProbe j) v)
    (externalCovariance ξ μ (ν.prod τ) (τ.map (fun v => ((q,j),v))) r s S anchor T
      (fun i => Q i.1.1) m base (dictionaryFactor D E u)
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f (extractionProbe j) 0)
  dsimp only [dictionaryFactor,v,probeHigh,probeLow] at hp hh hl' ⊢
  exact hh.trans (by linarith)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DictionaryExtraction
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators Topology
variable {Ω X Y Z : ℕ → Type} [∀ N, Fintype (Ω N)]
    [∀ N, MeasurableSpace (X N)] [∀ N, MeasurableSpace (Y N)]
    [∀ N, Countable (Z N)] [∀ N, MeasurableSpace (Z N)] [∀ N, MeasurableSingletonClass (Z N)]
    {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    {A : K → Type} [∀ q, Fintype (A q)] {L : ℕ} {M : ℕ → ℕ}
    (ξ : (N : ℕ) → Fin (M N) → Measure (Y N)) [∀ N j, IsProbabilityMeasure (ξ N j)]
    (μ : (N : ℕ) → Measure (X N)) [∀ N, IsProbabilityMeasure (μ N)]
    (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
    (τ : (N : ℕ) → Measure (Z N)) [∀ N, IsProbabilityMeasure (τ N)]
    (r s : ℕ → ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : (N : ℕ) → KernelTower (Ω N) L) (Q : (q : K) → Fin L → FiniteLaw (A q))
    (m : Fin (L+1) → ℝ)
    (base : (N : ℕ) → RootPath (Y N) (M N) → (k : ℕ) → RootPath (X N) k → FinitePath (Ω N) L → ℝ)
    (D E : (N : ℕ) → (q : K) → Z N → FinitePath (Ω N) L → FinitePath (A q) L → ℝ)
    (u : ℕ → K×ℕ → ℝ) (f : (N : ℕ) → (S.Leaf → FinitePath (Ω N) L) → ℝ)

 
theorem dictionary_coefficients_tendsto
    (hb : ∀ N k y, Measurable (fun z : RootPath (Y N) (M N) × RootPath (X N) k => base N z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ N x, |f N x| ≤ B)
    (hD : ∀ N q v x y, |D N q v x y| ≤ 1) (hE : ∀ N q v x y, |E N q v x y| ≤ 1)
    (hc : ∀ q j, 0 < ν.real {(q,j)}) (hs : ∀ N, 0 < s N)
    (he : ∀ q j, Tendsto (fun N => parameterError (ξ N) (μ N) (ν.prod (τ N)) (r N) (s N)
      (T N) (fun i => Q i.1.1) (fun l => m l.succ) (base N) Prod.fst
      (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
      (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (q,j) (u N) /
        (ν.real {(q,j)}*(s N:ℝ))) atTop (𝓝 0)) (q : K) (k : ℕ) :
    Tendsto (fun N => covarianceCoefficient (ξ N) (μ N) (ν.prod (τ N))
      ((τ N).map (fun v => ((q,0),v))) (r N) (s N) S anchor (T N) (fun i => Q i.1.1) m (base N)
      (dictionaryFactor (D N) (E N) (u N)) (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (f N) k)
      atTop (𝓝 0) := by
  let H (N : ℕ) (t : ℝ) := externalCovariance (ξ N) (μ N) (ν.prod (τ N))
    ((τ N).map (fun v => ((q,0),v))) (r N) (s N) S anchor (T N) (fun i => Q i.1.1) m (base N)
    (dictionaryFactor (D N) (E N) (u N)) (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (f N) t 0
  let coeff (N k : ℕ) := covarianceCoefficient (ξ N) (μ N) (ν.prod (τ N))
    ((τ N).map (fun v => ((q,0),v))) (r N) (s N) S anchor (T N) (fun i => Q i.1.1) m (base N)
    (dictionaryFactor (D N) (E N) (u N)) (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (f N) k
  let bound (k : ℕ) := 2*B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase anchor).card) (k+1)/(k.factorial:ℝ)
  let err (j N : ℕ) := B*(parameterError (ξ N) (μ N) (ν.prod (τ N)) (r N) (s N)
    (T N) (fun i => Q i.1.1) (fun l => m l.succ) (base N) Prod.fst
    (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
    (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (q,j) (u N) /
      (ν.real {(q,j)}*(s N:ℝ)))
  have hbound (k : ℕ) : 0 ≤ bound k := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) hB) (PrescribedTree.derivativeBound_nonneg _ _)
    · exact Nat.cast_nonneg _
  have hR (N k : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/2)) :
      |H N t - ∑ j ∈ Finset.range (k+1), coeff N j*t^j| ≤ bound k*t^(k+1) := by
    haveI : IsProbabilityMeasure ((τ N).map (fun v => ((q,0),v))) := Measure.isProbabilityMeasure_map (by fun_prop)
    exact externalCovariance_taylor_bound (ξ N) (μ N) (ν.prod (τ N))
      ((τ N).map (fun v => ((q,0),v))) (r N) (s N) S anchor (T N) (fun i => Q i.1.1) m (base N)
      (dictionaryFactor (D N) (E N) (u N)) (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2)
      (f N) (hb N) hm hmono hpos hroot hend hB (hf N) (fun i => hD N i.1.1 i.2)
      (fun i => hE N i.1.1 i.2) ht k
  apply coefficients_tendsto_zero_of_uniform_remainders H coeff bound (4*(4+8*(S.leaves:ℝ))*B)
    hbound (by positivity) hR err
    (fun j => by simpa only [mul_zero] using (he q j).const_mul B) _ k
  intro j N
  exact dictionary_covariance_probe_bound (ξ N) (μ N) ν (τ N) (r N) (s N) S anchor (T N) Q m
    (base N) (D N) (E N) (u N) (f N) q j (hb N) hm hmono hpos hroot hend hB (hf N)
    (hD N) (hE N) (hc q j) (hs N)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_VertexContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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

/-- The concrete selected-score producer implies vanishing of every literal
coefficient at each bounded old test, on every finite prescribed tree. -/
theorem physical_coefficients_tendsto_oai (S : PrescribedTree (L+1)) (anchor : S.Leaf)
    (M : Model p) (C H : ℝ) (Ns : ℕ → ℕ) (us : ℕ → K×ℕ → ℝ)
    (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
    (hm : ∀ l, 0 < m l) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n x, |f n x| ≤ B)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    (hw : ∀ j, 0 < ν.real {j})
    (he : ∀ j, Tendsto (fun n => scoreError ν Q m D E M C H j (Ns n+1) (us n)) atTop (𝓝 0))
    (q : K) (k : ℕ) :
    Tendsto (fun n => physicalCoefficient ν Q m D E S anchor M C H (Ns n+1) (us n) (f n) q k)
      atTop (𝓝 0) := by
  have hm0 : ∀ l, 0 ≤ m l := fun l => (hm l).le
  have hh (l : Fin (L+1)) : (Fin.cons 0 m : Fin (L+2) → ℝ) l.succ ≠ 0 := by
    simpa only [Fin.cons_succ] using (hm l).ne'
  have hend' : (Fin.cons 0 m : Fin (L+2) → ℝ) (Fin.last (L+1)) = 1 := by
    change m (Fin.last L) = 1
    exact hend
  have hs (n : ℕ) : 0 < scoreRate (Ns n+1) := by
    change 0 < scoreScale (Ns n+1)
    exact Real.rpow_pos_of_pos (by positivity) _
  simp only [physicalCoefficient, Nat.cast_add, Nat.cast_one]
  apply dictionary_coefficients_tendsto
    (fun n (_ : Fin (Ns n+1)) => M.field.toMeasure) (fun n => bondLaw M (Ns n+1)) ν
    (fun n => siteLaw (Ns n+1)) (fun n => M.alpha*(Ns n+1)) (fun n => scoreRate (Ns n+1))
    S anchor (fun n => KernelTower.terminalTower (fun _ : Fin (Ns n+1) => false) FiniteLaw.uniform L)
    Q (Fin.cons 0 m) (fun n => physicalBase M C H (Ns n+1))
    (fun n => observableAt D (Ns n+1)) (fun n => observableAt E (Ns n+1)) us f
    (fun n => measurable_physicalBase M C H (Ns n+1)) hh
    (exponent_cons_monotone m hm0 hmono) (exponent_cons_nonneg m hm0) (by simp) hend'
    hB hf (fun n q v x y => hD _ _ _) (fun n q v x y => hE _ _ _) (fun q j => hw (q,j)) hs _ q k
  intro q j
  convert he (q,j) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [scoreError,normalizedParameterError,Fin.cons_succ,
    scoreRate,markLaw,Nat.cast_add,Nat.cast_one]
  rfl

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.ConcreteReservoir.physical_coefficients_tendsto_oai := @OAI.DilutedSpinGlass.ConcreteReservoir.physical_coefficients_tendsto_oai
