-- Prove2me | solution 1 for OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:01:10.620473+00:00
-- url     : https://prove2.me/submissions/d0efd38e-2906-401f-a299-8ec165420a90

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

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    P.logMean m f ≤ P.logMean m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (P.expMoment_pos _ _)
  exact P.expect_mono (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h x) hm.le))

/-- Root-measurable uniform bounds pass unchanged through each power mean. -/
theorem logMean_stability {m c : ℝ} (hm : 0 < m) {f g : Ω → ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |P.logMean m f - P.logMean m g| ≤ c := by
  have hfg : P.logMean m f ≤ P.logMean m g + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).2; linarith)
  have hgf : P.logMean m g ≤ P.logMean m f + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

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



/-- Root-measurable homogeneous shifts pass through the whole backward recursion. -/
theorem backwardLog_add (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (f : FinitePath Ω n → ℝ) (c : ℝ) :
    backwardLog n T m (fun x => f x + c) = backwardLog n T m f + c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
        (fun y => f (x,y) + c)) =
        (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) + c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => f (x,y))
    rw [heq, FiniteLaw.logMean_add _ (hm 0)]

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

/-- The uniform insertion bound, with full arbitrary depth-dependent priors. -/
theorem backwardLog_stability (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f g : FinitePath Ω n → ℝ} {c : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ c) :
    |backwardLog n T m f - backwardLog n T m g| ≤ c := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    apply T.1.logMean_stability (hm 0)
    intro x
    exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => hfg (x,y))

/-- Pointwise bounds survive every backward step, uniformly in depth. -/
theorem backwardLog_bound (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f : FinitePath Ω n → ℝ} {c : ℝ}
    (hf : ∀ x, |f x| ≤ c) : |backwardLog n T m f| ≤ c := by
  have h := backwardLog_stability n T m hm (g := fun _ => 0)
    (fun x => by simpa only [sub_zero] using hf x)
  rwa [backwardLog_const n T m (fun i => ne_of_gt (hm i)), sub_zero] at h

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

/-- All orders, in the actual finite path-dependent kernel system. -/
theorem hasDerivAt_extensionIterate {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (k : ℕ) (S : PrescribedTree n) (G : Sample Ω S → ℝ)
    (u : ℝ) (hu : ∀ y, 0 < 1+u*D y) :
    HasDerivAt (extensionIterate T m D k S G) (extensionIterate T m D (k+1) S G u) u := by
  induction k generalizing S with
  | zero => exact hasDerivAt_fullyProtected S T m hm hroot hend D G u hu
  | succ k ih =>
    have hh := HasDerivAt.sum (u := Finset.univ) (fun v (_ : v ∈ (Finset.univ : Finset (Internal S))) =>
      (ih (grow S v) (fun x => G (oldSample S v x) * D (newPath S v x))).const_mul (gamma S m v))
    apply hh.congr_of_eventuallyEq
    filter_upwards [] with t
    simp only [Finset.sum_apply]
    rfl

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

end DilutedSpinGlass

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
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonVariance
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
open scoped BigOperators

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem logMean_uniform [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).logMean 1 f =
      Real.log (∑ a, Real.exp (f a))-Real.log (Fintype.card Ω) := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hsum : 0 < ∑ a, Real.exp (f a) := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [logMean,expMoment,expect,uniform,one_mul,div_one,← Finset.mul_sum]
  rw [Real.log_mul (inv_ne_zero hcard) (ne_of_gt hsum),Real.log_inv]
  ring
end FiniteLaw

end DilutedSpinGlass

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

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_10
theorem leaves_pos {n : ℕ} (S : PrescribedTree n) : 0 < leaves S := by
  induction S with
  | leaf => decide
  | @node n k C ih =>
    exact Finset.sum_pos (fun i _ => ih i) Finset.univ_nonempty

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

theorem fullyProtected_zero {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : FinitePath Ω n → ℝ) (G : Sample Ω S → ℝ) :
    fullyProtected S T m D G 0 = (sampleLaw S T).expect G := by
  simp [fullyProtected, KernelTower.tilt_const n T _ hm, leafSum_const]

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

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma charFunDual_iid_sum (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (L : StrongDual ℝ E) :
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L =
      charFunDual μ L ^ n := by
  rw [charFunDual_apply,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [map_sum,Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n => fun x : E => Complex.exp ((L x : ℂ)*Complex.I))]
  simp only [charFunDual_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma charFunDual_compoundPoisson (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : StrongDual ℝ E) :
    charFunDual (compoundPoisson r μ) L = Complex.exp ((r:ℂ)*(charFunDual μ L-1)) := by
  have hi : Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) (compoundPoisson r μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  change (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂compoundPoisson r μ) = _
  rw [compoundPoisson,integral_sum_measure hi]
  have hw (n : ℕ) : 0 ≤ Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial := by positivity
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal (hw _)]
  change (∑' n : ℕ, (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial) •
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L) = _
  simp_rw [charFunDual_iid_sum,Complex.real_smul]
  have hh := (NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*charFunDual μ L)).mul_left
    (Complex.exp (-(r:ℂ)))
  have he : (fun n : ℕ => ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial:ℝ):ℂ)*charFunDual μ L^n) =
      (fun n : ℕ => Complex.exp (-(r:ℂ))*(((r:ℂ)*charFunDual μ L)^n/n.factorial)) := by
    funext n
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
      Complex.ofReal_exp,Complex.ofReal_neg,mul_pow]
    ring
  rw [he,hh.tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ,← Complex.exp_add]
  congr 1
  ring
end DilutedSpinGlass

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
open _root_.MeasureTheory

namespace MeasureTheory
open scoped _root_.MeasureTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : _root_.MeasureTheory.Measure X) (ν : _root_.MeasureTheory.Measure Y) (ρ : _root_.MeasureTheory.Measure Z) [_root_.MeasureTheory.SFinite μ] [_root_.MeasureTheory.SFinite ν] [_root_.MeasureTheory.SFinite ρ]

lemma integrable_triple_rotate (F : (X×Y)×Z → ℝ) (hF : _root_.MeasureTheory.Integrable F ((μ.prod ν).prod ρ)) :
    _root_.MeasureTheory.Integrable (fun yz : Y×Z => ∫ x,F ((x,yz.1),yz.2) ∂μ) (ν.prod ρ) := by
  let G := F ∘ (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm
  have hG : _root_.MeasureTheory.Integrable G (μ.prod (ν.prod ρ)) :=
    (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc |>.integrable_comp_of_integrable hF
  exact hG.integral_prod_right

lemma integrable_triple_middle_swap (F : X×(Y×Z) → ℝ) (hF : _root_.MeasureTheory.Integrable F (μ.prod (ν.prod ρ))) :
    _root_.MeasureTheory.Integrable (fun xz : X×Z => ∫ y,F (xz.1,(y,xz.2)) ∂ν) (μ.prod ρ) := by
  have hid : _root_.MeasureTheory.MeasurePreserving (id : X → X) μ μ := ⟨measurable_id,_root_.MeasureTheory.Measure.map_id⟩
  have hG : _root_.MeasureTheory.Integrable (fun a : X×(Z×Y) => F (a.1,(a.2.2,a.2.1))) (μ.prod (ρ.prod ν)) :=
    (hid.prod (_root_.MeasureTheory.Measure.measurePreserving_swap (μ := ρ) (ν := ν))).integrable_comp_of_integrable hF
  have hH := (_root_.MeasureTheory.measurePreserving_prodAssoc μ ρ ν).integrable_comp_of_integrable hG
  exact hH.integral_prod_left

lemma integral_triple_rotate (F : (X×Y)×Z → ℝ) (hF : _root_.MeasureTheory.Integrable F ((μ.prod ν).prod ρ)) :
    (∫ a,∫ z,F (a,z) ∂ρ ∂μ.prod ν) =
      ∫ y,∫ z,∫ x,F ((x,y),z) ∂μ ∂ρ ∂ν := by
  let G := F ∘ (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm
  have hG : _root_.MeasureTheory.Integrable G (μ.prod (ν.prod ρ)) :=
    (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc |>.integrable_comp_of_integrable hF
  rw [← _root_.MeasureTheory.integral_prod _ hF]
  have he := (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).integral_comp' G
  change (∫ a,G (MeasurableEquiv.prodAssoc a) ∂(μ.prod ν).prod ρ)=_
  rw [he,_root_.MeasureTheory.integral_prod _ hG]
  rw [_root_.MeasureTheory.integral_integral_swap (f := fun x yz => G (x,yz)) hG]
  exact _root_.MeasureTheory.integral_prod _ hG.integral_prod_right

lemma integral_triple_middle_swap (F : X×(Y×Z) → ℝ) (hF : _root_.MeasureTheory.Integrable F (μ.prod (ν.prod ρ))) :
    (∫ x,∫ a,F (x,a) ∂ν.prod ρ ∂μ) =
      ∫ x,∫ z,∫ y,F (x,(y,z)) ∂ν ∂ρ ∂μ := by
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [hF.prod_right_ae] with x hx
  rw [_root_.MeasureTheory.integral_prod _ hx,_root_.MeasureTheory.integral_integral_swap hx]

end MeasureTheory

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
namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω Λ Γ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ]

theorem Projects.logMean {P : FiniteLaw Ω} {Q : FiniteLaw Λ} {π : Ω → Λ}
    (h : Projects P Q π) (m : ℝ) (f : Λ → ℝ) :
    P.logMean m (fun x => f (π x)) = Q.logMean m f := by
  unfold FiniteLaw.logMean FiniteLaw.expMoment
  rw [h (fun y => Real.exp (m*f y))]

lemma uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect f = (∑ x, f x)/(Fintype.card Ω) := by
  simp only [expect,uniform,← Finset.mul_sum]
  ring

end FiniteLaw

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_of_projects {π : Ω → Λ} (n : ℕ) {T : KernelTower Ω n} {U : KernelTower Λ n}
    (h : Projects π n T U) (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n T m (fun y => f (pathMap π n y)) = backwardLog n U m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.1.logMean (m 0) (fun a => backwardLog n (T.2 a) (fun j => m j.succ)
      (fun y => f (π a,pathMap π n y))) = _
    have heq : (fun a => backwardLog n (T.2 a) (fun j => m j.succ)
        (fun y => f (π a,pathMap π n y))) =
      (fun a => backwardLog n (U.2 (π a)) (fun j => m j.succ) (fun y => f (π a,y))) := by
      funext a
      exact ih (h.2 a) (fun j => m j.succ) (fun y => f (π a,y))
    rw [heq]
    exact h.1.logMean (m 0) (fun b => backwardLog n (U.2 b) (fun j => m j.succ) (fun y => f (b,y)))

end KernelTower
end DilutedSpinGlass
end

end

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
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinBaseComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw

lemma expect_uniform {B : Type} [Fintype B] [Nonempty B] (f : B → ℝ) :
    (uniform : FiniteLaw B).expect f = (∑ x, f x)/(Fintype.card B) := by
  simp only [expect,uniform,← Finset.mul_sum,div_eq_mul_inv]
  ring

end DilutedSpinGlass.FiniteLaw

end

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

noncomputable local instance qTreeLawDecidableEq_re22fea_1 (type : Type) :
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

theorem abs_qExpect_le {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {F : PrescribedTree n → ℝ} {C : ℝ} (hF : ∀ S, |F S| ≤ C)
    (k : ℕ) (S : PrescribedTree n) : |qExpect m F k S| ≤ C := by
  apply abs_le.mpr
  constructor
  · simpa only [qExpect_const m hroot hend] using
      qExpect_mono m hm hpos (fun S => (abs_le.mp (hF S)).1) k S
  · simpa only [qExpect_const m hroot hend] using
      qExpect_mono m hm hpos (fun S => (abs_le.mp (hF S)).2) k S

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

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLogExpansion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type}
open scoped BigOperators

theorem leafProduct_single (n : ℕ) (f : FinitePath Ω n → ℝ) (x : Sample Ω (single n)) :
    leafProduct (single n) f x = f (singlePath n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∏ i : Fin 1, leafProduct (single n) (fun y => f ((x i).1,y)) (x i).2) = _
    rw [Fintype.prod_subsingleton]
    exact ih _ _

private theorem leafProduct_cast {n : ℕ} (S S' : PrescribedTree n) (h : S' = S)
    (f : FinitePath Ω (n+1) → ℝ) (x : Ω × Sample Ω S') :
    leafProduct S' (fun y => f (x.1,y)) x.2 =
    leafProduct S (fun y => f ((cast (congrArg (fun R => Ω × Sample Ω R) h) x).1,y))
      (cast (congrArg (fun R => Ω × Sample Ω R) h) x).2 := by
  subst S'
  rfl

/-- Exactly one terminal factor is added by growth, and its ancestry is the
new path, not a path chosen by equality of sample values. -/
theorem leafProduct_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω (grow S v)) :
    leafProduct (grow S v) f x = leafProduct S f (oldSample S v x) * f (newPath S v x) := by
  classical
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (∏ j : Fin (k+1), leafProduct (Fin.cases (single n) C j)
        (fun y => f ((x j).1,y)) (x j).2) = _
      erw [Fin.prod_univ_succ]
      have hh := leafProduct_single n (fun y => f ((x 0).1,y)) (x 0).2
      calc
        _ = f ((x 0).1,singlePath n (x 0).2) *
            ∏ i : Fin k, leafProduct (C i) (fun y => f ((x i.succ).1,y)) (x i.succ).2 :=
          congrArg₂ (· * ·) hh rfl
        _ = _ := mul_comm _ _
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      have hp (j : Fin k) :
          leafProduct (C' j) (fun y => f ((x j).1,y)) (x j).2 =
          leafProduct (C j) (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 *
              if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 1 := by
        by_cases hj : j = i
        · subst j
          have hcast := leafProduct_cast (grow (C i) v) (C' i)
            (Function.update_self ..) f (x i)
          let y : Ω × Sample Ω (grow (C i) v) :=
            cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
          have hh := ih i v (fun z => f (y.1,z)) y.2
          have he : leafProduct (C' i) (fun z => f ((x i).1,z)) (x i).2 =
              leafProduct (C i) (fun z => f (y.1,z)) (oldSample (C i) v y.2) *
                f (y.1,newPath (C i) v y.2) := hcast.trans hh
          erw [oldSample.eq_1, newPath.eq_1]
          dsimp only [id]
          simp only [dite_true, ite_true]
          exact he
        · have hc := leafProduct_cast (C j) (C' j) (Function.update_of_ne hj ..) f (x j)
          erw [oldSample.eq_1]
          dsimp only [id]
          simp only [dite_eq_right hj, ite_eq_right hj, mul_one]
          exact hc
      change (∏ j, leafProduct (C' j) (fun y => f ((x j).1,y)) (x j).2) = _
      calc
        _ = ∏ j, (leafProduct (C j)
            (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 *
            if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 1) :=
          Finset.prod_congr rfl (fun j _ => hp j)
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', ite_eq_left (Finset.mem_univ i)]; rfl


end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem abs_leafProduct_le_one {n : ℕ} (S : PrescribedTree n)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (x : Sample Ω S) :
    |leafProduct S D x| ≤ 1 := by
  rw [leafProduct_eq_prod, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hD _)

theorem abs_qMoment_le_one {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) (T : KernelTower Ω n)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    (k : ℕ) (S : PrescribedTree n) : |qMoment m T D k S| ≤ 1 :=
  abs_qExpect_le m hm hpos hroot hend (fun R =>
    FiniteLaw.abs_expect_le _ (abs_leafProduct_le_one R D hD)) k S

/-- Exact coefficients of all genuine fresh growth histories. Normalizing at
successive tree sizes produces the rising factorial, with no guessed law. -/
theorem extensionIterate_eq_qMoment {n : ℕ} (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (T : KernelTower Ω n)
    (D : FinitePath Ω n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    extensionIterate T m D k S (leafProduct S D) 0 =
      (-1:ℝ)^k * ((leaves S).ascFactorial k:ℝ) * qMoment m T D k S := by
  induction k generalizing S with
  | zero => simp [extensionIterate, fullyProtected_zero S T m hnz, qMoment, qExpect]
  | succ k ih =>
    change (∑ v : Internal S, gamma S m v *
      extensionIterate T m D k (grow S v)
        (fun x => leafProduct S D (oldSample S v x) * D (newPath S v x)) 0) = _
    have hg (v : Internal S) : (fun x => leafProduct S D (oldSample S v x) *
        D (newPath S v x)) = leafProduct (grow S v) D :=
      funext (fun x => (leafProduct_grow S v D x).symm)
    simp_rw [hg, ih, leaves_grow]
    have hfac : ((leaves S).ascFactorial (k+1):ℝ) =
        (leaves S:ℝ) * ((leaves S+1).ascFactorial k:ℝ) := by
      rw [Nat.ascFactorial_succ]
      exact_mod_cast (Nat.succ_ascFactorial (leaves S) k).symm
    rw [hfac]
    change _ = _ * (∑ v : Internal S, (-gamma S m v / leaves S) *
      qMoment m T D k (grow S v))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    have hn : (leaves S:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (leaves_pos S))
    rw [pow_succ]
    field_simp

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators

theorem analyticAt_expect (P : FiniteLaw Ω) {f : ℝ → Ω → ℝ} {u : ℝ}
    (hf : ∀ x, AnalyticAt ℝ (fun t => f t x) u) :
    AnalyticAt ℝ (fun t => P.expect (f t)) u := by
  apply Finset.analyticAt_fun_sum
  intro x _
  exact analyticAt_const.mul (hf x)

theorem analyticAt_logMean (P : FiniteLaw Ω) (m : ℝ) {f : ℝ → Ω → ℝ} {u : ℝ}
    (hf : ∀ x, AnalyticAt ℝ (fun t => f t x) u) :
    AnalyticAt ℝ (fun t => P.logMean m (f t)) u := by
  have he : AnalyticAt ℝ (fun t => P.expMoment m (f t)) u :=
    P.analyticAt_expect (fun x => (analyticAt_const.mul (hf x)).rexp')
  exact (he.log (P.expMoment_pos m (f u))).div_const
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

theorem analyticAt_backwardLog (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) {f : ℝ → FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, AnalyticAt ℝ (fun t => f t x) u) :
    AnalyticAt ℝ (fun t => backwardLog n T m (f t)) u := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact T.1.analyticAt_logMean (m 0)
      (fun x => ih (T.2 x) (fun j => m j.succ) (fun y => hf (x,y)))
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators Topology NNReal ENNReal
open Set Filter

theorem fullyProtected_single {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) {u : ℝ} (hu : ∀ y, 0 < 1+u*D y) :
    fullyProtected (single n) T m D (leafProduct (single n) D) u =
      (KernelTower.law n (KernelTower.tilt n T (fun j => m j.succ)
        (fun y => Real.log (1+u*D y)))).expect (fun y => D y / (1+u*D y)) := by
  rw [fullyProtected]
  trans (sampleLaw (single n) (KernelTower.tilt n T (fun j => m j.succ)
    (fun y => Real.log (1+u*D y)))).expect
      (fun x => D (singlePath n x) / (1+u*D (singlePath n x)))
  · apply FiniteLaw.expect_congr
    intro x
    rw [leafProduct_single, leafSum_single, Real.exp_neg, Real.exp_log (hu _)]
    rfl
  · exact single_expect (Ω := Ω) n _ (fun y => D y / (1+u*D y))

theorem hasDerivAt_logJet {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (k : ℕ) {u : ℝ} (hu : ∀ y, 0 < 1+u*D y) :
    HasDerivAt (logJet T m D k) (logJet T m D (k+1) u) u := by
  cases k with
  | zero =>
    change HasDerivAt (logInsertion T m D)
      (fullyProtected (single n) T m D (leafProduct (single n) D) u) u
    rw [fullyProtected_single T m D hu]
    apply KernelTower.hasDerivAt_backwardLog n T _ hnz
    intro y
    simpa only [zero_add, one_mul, Pi.add_apply, id_eq] using
      ((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).mul_const (D y))).log
        (ne_of_gt (hu y))
  | succ k => exact hasDerivAt_extensionIterate T m hnz hroot hend D k _ _ u hu

omit [Fintype Ω] in
theorem insertion_pos {n : ℕ} (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {u : ℝ} (hu : |u| < 1) (y : FinitePath Ω n) : 0 < 1+u*D y := by
  have h : |u * D y| ≤ |u| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hD y) (abs_nonneg u)).trans_eq (mul_one _)
  have hb := (abs_le.mp h).1
  linarith

theorem iteratedDeriv_logInsertion {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (k : ℕ) :
    EqOn (iteratedDeriv k (logInsertion T m D)) (logJet T m D k) (Ioo (-1) 1) := by
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
    intro u hu
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (logInsertion T m D) =ᶠ[𝓝 u] logJet T m D k :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo (-1) 1, isOpen_Ioo.mem_nhds hu, ih⟩
    rw [he.deriv_eq]
    exact (hasDerivAt_logJet T m hnz hroot hend D k
      (insertion_pos D hD (abs_lt.mpr hu))).deriv

 
theorem logInsertion_coefficient {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (k : ℕ) :
    iteratedDeriv (k+1) (logInsertion T m D) 0 / ((k+1).factorial:ℝ) =
      (-1:ℝ)^k / (k+1) * qMoment m T D k (single n) := by
  rw [iteratedDeriv_logInsertion T m hnz hroot hend D hD (k+1) (by norm_num)]
  change extensionIterate T m D k (single n) (leafProduct (single n) D) 0 / _ = _
  rw [extensionIterate_eq_qMoment m hnz T D k, leaves_single, Nat.one_ascFactorial,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hk : (k.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk1 : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators Topology NNReal ENNReal
open Set Filter

theorem logInsertion_zero {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (D : FinitePath Ω n → ℝ) :
    logInsertion T m D 0 = 0 := by
  simp only [logInsertion, zero_mul, add_zero, Real.log_one]
  exact KernelTower.backwardLog_const n T _ hnz 0

theorem logInsertion_coefficient_bound {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (k : ℕ) :
    |iteratedDeriv k (logInsertion T m D) 0 / (k.factorial:ℝ)| ≤ 1 := by
  cases k with
  | zero => simp [logInsertion_zero T m hnz D]
  | succ k =>
    rw [logInsertion_coefficient T m hnz hroot hend D hD k, abs_mul, abs_div,
      abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity : (0:ℝ) < k+1)]
    calc
      _ ≤ 1 / ((k:ℝ)+1) * 1 := mul_le_mul_of_nonneg_left
        (abs_qMoment_le_one m hm hpos hroot hend T D hD k (single n)) (by positivity)
      _ ≤ 1 := by rw [mul_one]; exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

theorem analyticAt_logInsertion {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {t : ℝ} (ht : |t| < 1) : AnalyticAt ℝ (logInsertion T m D) t := by
  apply KernelTower.analyticAt_backwardLog
  intro y
  exact (analyticAt_const.add (analyticAt_id.mul analyticAt_const)).log
    (insertion_pos D hD ht y)

/-- The positive Q tree expansion of the nonlinear power means, valid on the
whole physical |t|<1 disk, not merely its unspecified Taylor neighborhood. -/
theorem hasSum_logInsertion {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun k => (-1:ℝ)^k / (k+1) * qMoment m T D k (single n) * t^(k+1))
      (logInsertion T m D t) := by
  let c (k : ℕ) := iteratedDeriv k (logInsertion T m D) 0 / (k.factorial:ℝ)
  let p := FormalMultilinearSeries.ofScalars ℝ c
  have hrad : 1 ≤ p.radius := by
    exact p.le_radius_of_bound (r := (1:ℝ≥0)) 1 (fun k => by
      simpa only [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
        NNReal.coe_one, one_pow, mul_one] using
        logInsertion_coefficient_bound T m hm hpos hnz hroot hend D hD k)
  have ha : AnalyticOn ℝ (logInsertion T m D) (Metric.eball 0 1) := by
    intro x hx
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal] at hx
    exact (analyticAt_logInsertion T m D hD (by simpa [Real.dist_eq] using hx)).analyticWithinAt
  have hp : HasFPowerSeriesOnBall (logInsertion T m D) p 0 1 :=
    ha.hasFPowerSeriesOnSubball (by norm_num) hrad
  have htt : t ∈ Metric.eball (0:ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq] using ht
  have hs : HasSum (fun k => c k * t^k) (logInsertion T m D t) := by
    simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq, sub_zero,
      smul_eq_mul] using hp.hasSum_sub htt
  have hc0 : c 0 * t^0 = 0 := by simp [c, logInsertion_zero T m hnz D]
  have hs' : HasSum (fun k => c (k+1) * t^(k+1)) (logInsertion T m D t) := by
    simpa only [Finset.sum_range_one, hc0, sub_zero] using
      (hasSum_nat_add_iff' 1).mpr hs
  simpa only [c, logInsertion_coefficient T m hnz hroot hend D hD] using hs'

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators

theorem logInsertion_term_bound {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (t : ℝ) (k : ℕ) :
    |(-1:ℝ)^k / (k+1) * qMoment m T D k (single n) * t^(k+1)| ≤
      |t|^(k+1) / (k+1) := by
  rw [abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity : (0:ℝ) < k+1), abs_pow]
  calc
    _ ≤ (1 / ((k:ℝ)+1) * 1) * |t|^(k+1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (abs_qMoment_le_one m hm hpos hroot hend T D hD k (single n))
        (by positivity)) (by positivity)
    _ = _ := by ring

 
theorem logInsertion_tail_bound {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) {t : ℝ} (ht : |t| < 1) (K : ℕ) :
    |logInsertion T m D t - ∑ k ∈ Finset.range K,
      (-1:ℝ)^k / (k+1) * qMoment m T D k (single n) * t^(k+1)| ≤
        ∑' k : ℕ, |t|^(k+K+1) / (k+K+1) := by
  let f (k : ℕ) := (-1:ℝ)^k / (k+1) * qMoment m T D k (single n) * t^(k+1)
  let g (k : ℕ) := |t|^(k+1) / (k+1)
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le (fun k => by dsimp [g]; positivity) _
      ((summable_geometric_of_lt_one (abs_nonneg t) ht).mul_left |t|)
    intro k
    dsimp [g]
    rw [pow_succ, mul_comm]
    exact div_le_self (by positivity) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hs : HasSum f (logInsertion T m D t) :=
    hasSum_logInsertion T m hm hpos hnz hroot hend D hD ht
  have htail : logInsertion T m D t - ∑ k ∈ Finset.range K, f k =
      ∑' k, f (k+K) := by
    rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add K]
    ring
  change |logInsertion T m D t - ∑ k ∈ Finset.range K, f k| ≤ _
  rw [htail]
  have hgtail : Summable (fun k => g (k+K)) := (summable_nat_add_iff K).mpr hg
  have hftail : Summable (fun k => f (k+K)) := (summable_nat_add_iff K).mpr hs.summable
  have hb := hftail.abs.tsum_le_tsum (fun k =>
    logInsertion_term_bound T m hm hpos hroot hend D hD t (k+K))
      hgtail
  have habsn : Summable (fun k => ‖f (k+K)‖) := by
    simpa only [Real.norm_eq_abs] using hftail.abs
  have habs : |∑' k, f (k+K)| ≤ ∑' k, |f (k+K)| := by
    simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm habsn)
  exact habs.trans (by simpa only [f, g, Nat.cast_add, Nat.cast_one] using hb)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Set
open scoped NNReal BigOperators

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

noncomputable local instance finiteEncodingDecidableEq_re22fea_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma integral_asProbability {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : FiniteLaw Ω) (f : Ω → X) (g : X → ℝ) :
    ∫ x, g x ∂(P.asProbability f)=P.expect (fun a => g (f a)) := by
  rw [asProbability,integral_atomicProbability]
  rfl

end FiniteLaw

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QSubtreePotential
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

lemma asProbability_id_singleton [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : FiniteLaw Ω) (a : Ω) : (P.asProbability id).toMeasure {a} = ENNReal.ofReal (P.weight a) := by
  classical
  simp [asProbability, atomicProbability, nnWeights, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton a), Pi.single_apply]
  exact ENNReal.ofReal_coe_nnreal.symm

lemma asProbability_eq_map [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {X : Type*} [MeasurableSpace X] (P : FiniteLaw Ω) (f : Ω → X) :
    (P.asProbability f).toMeasure = Measure.map f (P.asProbability id).toMeasure := by
  classical
  have hf : Measurable f := measurable_of_countable f
  simp only [asProbability, atomicProbability]
  change (∑ a, ((P.nnWeights).val a : ℝ≥0∞) • Measure.dirac (f a)) =
    Measure.map f (∑ a, ((P.nnWeights).val a : ℝ≥0∞) • Measure.dirac a)
  rw [Measure.map_finset_sum hf.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' hf]

lemma asProbability_pi {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → X i) :
    ((pi Q).asProbability (fun x i => f i (x i))).toMeasure =
      Measure.pi (fun i => ((Q i).asProbability (f i)).toMeasure) := by
  classical
  let (index : ι) : MeasurableSpace (α index) := ⊤
  let (index : ι) : MeasurableSingletonClass (α index) := ⟨fun _ => trivial⟩
  have he : ((pi Q).asProbability id).toMeasure =
      Measure.pi (fun i => ((Q i).asProbability id).toMeasure) := by
    apply Measure.ext_of_singleton
    intro x
    simp only [asProbability_id_singleton, Measure.pi_singleton]
    change ENNReal.ofReal (∏ i, (Q i).weight (x i)) = _
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Q i).nonneg _)]
  rw [asProbability_eq_map, he, Measure.pi_map_pi (fun i =>
    (measurable_of_countable (f i)).aemeasurable)]
  simp_rw [← asProbability_eq_map]

lemma integral_pi_asProbability {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → X i)
    (g : ((i : ι) → X i) → ℝ) :
    (∫ x, g x ∂Measure.pi (fun i => ((Q i).asProbability (f i)).toMeasure)) =
      (pi Q).expect (fun a => g (fun i => f i (a i))) := by
  rw [← asProbability_pi, integral_asProbability]

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TopologyDecay
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace FiniteLaw
variable {Ω β : Type} [Fintype Ω] [Fintype β]

attribute [local instance] OAI.DilutedSpinGlass.finiteMapDecEq
lemma expect_map (P : FiniteLaw Ω) (f : Ω → β) (g : β → ℝ) :
    (P.map f).expect g=P.expect (fun a => g (f a)) := by
  classical
  change (∑ b, P.expect (fun a => if f a=b then 1 else 0)*g b)=_
  simp_rw [← expect_mul_right]
  rw [← expect_fintype_sum]
  apply expect_congr
  intro a
  simp

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n : ℕ}

lemma integrable_qExpect (μ : Measure Z) (m : Fin (n+1) → ℝ)
    (F : Z → PrescribedTree n → ℝ) (hF : ∀ T, Integrable (fun z => F z T) μ)
    (k : ℕ) (S : PrescribedTree n) : Integrable (fun z => qExpect m (F z) k S) μ := by
  induction k generalizing S with
  | zero => exact hF S
  | succ k ih => exact integrable_finsetSum _ (fun v _ => (ih (grow S v)).const_mul _)

lemma integral_qExpect (μ : Measure Z) (m : Fin (n+1) → ℝ)
    (F : Z → PrescribedTree n → ℝ) (hF : ∀ T, Integrable (fun z => F z T) μ)
    (k : ℕ) (S : PrescribedTree n) :
    (∫ z, qExpect m (F z) k S ∂μ) = qExpect m (fun T => ∫ z, F z T ∂μ) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect]
    rw [integral_finsetSum _ (fun v _ =>
      (integrable_qExpect μ m F hF k (grow S v)).const_mul _)]
    simp only [integral_const_mul,ih]

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteTowerPi
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {ι Ω : Type}

variable [Fintype ι] [DecidableEq ι] [Fintype Ω]

lemma sampleLaw_piTower_weight {n : ℕ} (S : PrescribedTree n)
    (T : ι → KernelTower Ω n) (x : Sample (ι → Ω) S) :
    (S.sampleLaw (KernelTower.piTower n T)).weight x =
      ∏ i,(S.sampleLaw (T i)).weight (sampleMap (fun y : ι → Ω => y i) S x) := by
  induction S with
  | leaf => simp [sampleLaw,KernelTower.unitLaw]
  | @node n k C ih =>
    change (∏ j, (∏ i,(T i).1.weight ((x j).1 i))*
      ((C j).sampleLaw (KernelTower.piTower n (fun i => (T i).2 ((x j).1 i)))).weight (x j).2) =
      ∏ i,∏ j,(T i).1.weight ((x j).1 i)*
        ((C j).sampleLaw ((T i).2 ((x j).1 i))).weight (sampleMap (fun y : ι → Ω => y i) (C j) (x j).2)
    simp_rw [ih,← Finset.prod_mul_distrib]
    exact Finset.prod_comm

lemma sampleExpect_piTower {n : ℕ} (S : PrescribedTree n)
    (T : ι → KernelTower Ω n) (f : Sample (ι → Ω) S → ℝ) :
    (S.sampleLaw (KernelTower.piTower n T)).expect f =
      (FiniteLaw.pi (fun i => S.sampleLaw (T i))).expect (fun x => f (samplePi S x)) := by
  unfold FiniteLaw.expect
  apply Fintype.sum_equiv (samplePiEquiv S)
  intro x
  simp only [samplePiEquiv,Equiv.coe_fn_mk,samplePi_eval,FiniteLaw.pi,sampleLaw_piTower_weight]

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RealEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Set TopologicalSpace
open scoped BigOperators NNReal
attribute [local instance] OAI.DilutedSpinGlass.realEncodingMeasurableSpace
local instance realEncodingBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

attribute [local instance] OAI.DilutedSpinGlass.realEncodingMeasurableSpace
lemma backwardLog_realEncode {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i,Fintype (α i)] (r : ℕ)
    (T : (i : ι) → KernelTower (α i) r) (V : (i : ι) → FinitePath (α i) r → ℝ)
    (F : (ι → ℝ) → ℝ) (m : Fin r → ℝ) :
    backwardLog r (pi r T) m (fun y => F (fun i => V i (FinitePath.proj r y i))) =
      DilutedSpinGlass.logMean r F m (fun i => realEncode r (T i) (V i)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (i : ι) → FiniteLaw (α i) × (α i → KernelTower (α i) r) at T
    change (i : ι) → (α i × FinitePath (α i) r) → ℝ at V
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun a => backwardLog r (pi r (fun i => (T i).2 (a i))) (fun j => m j.succ)
        (fun y => F (fun i => V i (a i,FinitePath.proj r y i)))) =
      Real.log (∫ x, Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ) x)
        ∂Measure.pi (fun i => ((T i).1.asProbability
          (fun a => realEncode r ((T i).2 a) (fun y => V i (a,y)))).toMeasure)) / m 0
    have hc (a : (i : ι) → α i) := ih (fun i => (T i).2 (a i))
      (fun i y => V i (a i,y)) (fun j => m j.succ)
    simp_rw [hc]
    change Real.log ((FiniteLaw.pi (fun i => (T i).1)).expect (fun a =>
      Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ)
        (fun i => realEncode r ((T i).2 (a i)) (fun y => V i (a i,y)))))) / m 0 =
      Real.log (∫ x, Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ) x)
        ∂Measure.pi (fun i => ((T i).1.asProbability
          (fun a => realEncode r ((T i).2 a) (fun y => V i (a,y)))).toMeasure)) / m 0
    rw [FiniteLaw.integral_pi_asProbability]

end KernelTower

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

lemma qExpect_leaf_power {n : ℕ} (m : Fin (n+1) → ℝ)
    (F : PrescribedTree n → ℝ) (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun R => c^R.leaves*F R) k S = c^(S.leaves+k)*qExpect m F k S := by
  induction k generalizing S with
  | zero => simp [qExpect]
  | succ k ih =>
    simp only [qExpect,ih,leaves_grow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [show S.leaves+1+k=S.leaves+(k+1) by omega]
    ring

variable {Ω : Type} [Fintype Ω]
lemma qMoment_neg {n : ℕ} (m : Fin (n+1) → ℝ) (T : KernelTower Ω n)
    (D : FinitePath Ω n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    qMoment m T (fun y => -D y) k S=(-1:ℝ)^(S.leaves+k)*qMoment m T D k S := by
  unfold qMoment
  have he (R : PrescribedTree n) :
      (sampleLaw R T).expect (leafProduct R (fun y => -D y))=
        (-1:ℝ)^R.leaves*(sampleLaw R T).expect (leafProduct R D) := by
    rw [← FiniteLaw.expect_mul_left]
    apply FiniteLaw.expect_congr
    intro x
    simp only [leafProduct_eq_prod,Finset.prod_neg,Finset.card_univ,card_leaf]
  simp_rw [he]
  exact qExpect_leaf_power _ _ _ _ _

lemma logInsertion_negative_tail {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y,|D y|≤1) {t : ℝ} (ht : |t|<1) (K : ℕ) :
    |logInsertion T m D t - ∑ k∈Finset.range K,
      -(t^(k+1)/(k+1))*qMoment m T (fun y => -D y) k (single n)| ≤
      ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
  convert logInsertion_tail_bound T m hm hpos hnz hroot hend D hD ht K using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [qMoment_neg,leaves_single]
  rw [show 1+k=k+1 by omega,pow_succ (-1:ℝ)]
  ring

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma map_familyLaw_sum {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : Type*} [MeasurableSpace Y] (μ : Measure I) (ν : ∀ i, Measure (X i))
    (f : (i : I) → X i → Y) (hf : ∀ i, Measurable (f i)) :
    Measure.map (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) =
      Measure.sum (fun i => μ {i} • Measure.map (f i) (ν i)) := by
  rw [familyLaw,Measure.comp_eq_sum_of_countable]
  rw [Measure.map_sum (measurable_sigmaUncurry hf).aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul]
  change μ {i} • Measure.map (fun z : Sigma X => f z.1 z.2)
    (Measure.map (Sigma.mk i) (ν i)) = _
  rw [Measure.map_map (measurable_sigmaUncurry hf) (measurable_sigmaMk i)]
  rfl

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_NormalizedCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped BigOperators

lemma convex_pow_tangent {p : ℕ} (hp : Even p) (x y : ℝ) :
    (p:ℝ)*y^(p-1)*(x-y) ≤ x^p-y^p := by
  have hc : ConvexOn ℝ Set.univ (fun t : ℝ => t^p) := hp.convexOn_pow
  have hd : HasDerivAt (fun t : ℝ => t^p) ((p:ℝ)*y^(p-1)) y := hasDerivAt_pow p y
  rcases lt_trichotomy y x with h | h | h
  · have hh := hc.le_slope_of_hasDerivAt (mem_univ y) (mem_univ x) h hd
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr h)).mp hh
  · subst x
    simp
  · have hh := hc.slope_le_of_hasDerivAt (mem_univ x) (mem_univ y) h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp (show (y^p-x^p)/(y-x)≤(p:ℝ)*y^(p-1) from hh)
    nlinarith

 
lemma even_cavity_remainder_nonneg {p : ℕ} (hp : Even p) (hp1 : 1≤p) (P B : ℝ) :
    0 ≤ P^p-(p:ℝ)*P*B^(p-1)+((p-1:ℕ):ℝ)*B^p := by
  have ht := convex_pow_tangent hp P B
  have he : B^(p-1)*B=B^p := by rw [← pow_succ,Nat.sub_add_cancel hp1]
  rw [Nat.cast_sub hp1,Nat.cast_one]
  nlinarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma measurable_factorCut (R : ℝ) : Measurable (factorCut R) :=
  measurable_id.ite (measurableSet_le measurable_norm measurable_const) measurable_const

lemma factorCut_product {p : ℕ} (R b : ℝ) (f : Fin p → Spin → ℝ) (s : Fin p → Spin) :
    b*(∏ l,factorCut R (f l) (s l)) =
      if ∀ l,‖f l‖≤R then b*∏ l,f l (s l) else 0 := by
  classical
  by_cases h : ∀ l,‖f l‖≤R
  · simp [factorCut,h]
  · obtain ⟨j,hj⟩ := not_forall.mp h
    have hz : ∏ l,factorCut R (f l) (s l) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [factorCut,hj])
    simp [h,hz]

lemma factorCut_product_lt_one {p : ℕ} (R b : ℝ) (f : Fin p → Spin → ℝ)
    (h : ∀ s : Fin p → Spin,|b*∏ l,f l (s l)|<1) :
    ∀ s : Fin p → Spin,|b*∏ l,factorCut R (f l) (s l)|<1 := by
  intro s
  rw [factorCut_product]
  split_ifs
  · exact h s
  · norm_num

lemma measurable_patternFeature {n : ℕ} (R : ℝ) (P : FiniteLaw (Fin n → Spin)) :
    Measurable (patternFeature R P) := by
  unfold patternFeature FiniteLaw.expect
  apply Finset.measurable_sum
  intro s _
  apply Measurable.const_mul
  exact Finset.measurable_prod _ (fun a _ => (measurable_pi_apply (s a)).comp (measurable_factorCut R))

/-- Independence of b and the iid factors, applied to actual measurable
coordinate tests rather than assuming a replica coefficient formula. -/
lemma integral_b_factors {p : ℕ} (M : Model p) (hM : Admissible M) (n : ℕ)
    (g : Fin p → (Spin → ℝ) → ℝ) (hg : ∀ l,Measurable (g l)) :
    (∫ z : InteractionSample p,(-z.2.2.1)^n*(∏ l,g l (z.2.2.2 l)) ∂M.disorder.toMeasure) =
      (∫ z : InteractionSample p,(-z.2.2.1)^n ∂M.disorder.toMeasure)*
      ∏ l,∫ z : InteractionSample p,g l (z.2.2.2 l) ∂M.disorder.toMeasure := by
  have hgm : Measurable (fun f : Fin p → Spin → ℝ => ∏ l,g l (f l)) :=
    Finset.measurable_prod _ (fun l _ => (hg l).comp (measurable_pi_apply l))
  have hb := hM.independent_b.comp (show Measurable (fun b : ℝ => (-b)^n) by fun_prop) hgm
  have he := hb.integral_fun_mul_eq_mul_integral
    (show AEStronglyMeasurable (fun z : InteractionSample p => (-z.2.2.1)^n) M.disorder.toMeasure by fun_prop)
    (show AEStronglyMeasurable (fun z : InteractionSample p => ∏ l,g l (z.2.2.2 l)) M.disorder.toMeasure from
      (hgm.comp (by fun_prop)).aestronglyMeasurable)
  simp only [Function.comp_def] at he
  rw [he,hM.independent_f.integral_fun_prod_comp (fun l => by fun_prop) (fun l => (hg l).aestronglyMeasurable)]

lemma integral_factor_coordinate {p : ℕ} (M : Model p) (hM : Admissible M)
    (j l : Fin p) (g : (Spin → ℝ) → ℝ) (hg : Measurable g) :
    (∫ z : InteractionSample p,g (z.2.2.2 l) ∂M.disorder.toMeasure) =
      ∫ z : InteractionSample p,g (z.2.2.2 j) ∂M.disorder.toMeasure :=
  ((hM.identically_distributed_f l j).comp hg).integral_eq

/-- All coordinates may use different replica-pattern laws. This includes the
old spin replicas and fresh message replicas on every prescribed topology. -/
lemma upper_pattern_moment {p n : ℕ} (M : Model p) (hM : Admissible M)
    (j : Fin p) (R : ℝ) (P : Fin p → FiniteLaw (Fin n → Spin)) :
    (∫ z : InteractionSample p,(-z.2.2.1)^n*
      (FiniteLaw.pi P).expect (fun s => ∏ a : Fin n,∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a))
      ∂M.disorder.toMeasure) =
      (∫ z : InteractionSample p,(-z.2.2.1)^n ∂M.disorder.toMeasure)*
      ∏ l,∫ z : InteractionSample p,patternFeature R (P l) (z.2.2.2 j) ∂M.disorder.toMeasure := by
  have he (z : InteractionSample p) :
      (FiniteLaw.pi P).expect (fun s => ∏ a : Fin n,∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a)) =
      ∏ l,patternFeature R (P l) (z.2.2.2 l) := by
    conv_lhs => arg 2; ext s; rw [Finset.prod_comm]
    exact FiniteLaw.expect_pi_product P (fun l s => ∏ a, factorCut R (z.2.2.2 l) (s a))
  simp_rw [he]
  rw [integral_b_factors M hM n (fun l => patternFeature R (P l)) (fun l => measurable_patternFeature R (P l))]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  exact integral_factor_coordinate M hM j l _ (measurable_patternFeature R (P l))

lemma product_one_distinguished {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) (P B : ℝ) :
    (∏ l : ι,if l=j then P else B)=P*B^(Fintype.card ι-1) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [↓reduceIte]
  congr 1
  have he : (∏ l ∈ Finset.univ.erase j,if l=j then P else B) = ∏ _l ∈ Finset.univ.erase j,B := by
    apply Finset.prod_congr rfl
    intro l hl
    simp only [(Finset.mem_erase.mp hl).1,↓reduceIte]
  rw [he,Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FinitePoissonSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma integral_finiteUniform {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : A → E) :
    (∫ x, f x ∂finiteUniform A) = ((Fintype.card A:ℝ)⁻¹) • ∑ x,f x := by
  rw [finiteUniform,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Finset.smul_sum]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityRateLimits
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory

lemma appendSpin_castSucc {q : ℕ} (s : Fin q → Spin) (ε : Spin) (i : Fin q) :
    appendSpin (p := q+1) s ε i.castSucc = s i := by
  simp only [appendSpin,Nat.add_sub_cancel,Fin.val_castSucc,dite_eq_left i.isLt]
  rfl

lemma appendSpin_last {q : ℕ} (s : Fin q → Spin) (ε : Spin) :
    appendSpin (p := q+1) s ε (Fin.last q) = ε := by
  simp [appendSpin]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProductLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

lemma integral_root_prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (n : ℕ) (F : (Fin n → X) × (Fin n → Y) → ℝ)
    (hF : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => ν)))) :
    (∫ z : RootPath (X×Y) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod ν)) =
      ∫ x : Fin n → X,∫ y : Fin n → Y,F (x,y)
        ∂Measure.pi (fun _ : Fin n => ν) ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_rootArray_eq_pi (μ.prod ν) n (fun z : Fin n → X×Y => F ((fun i => (z i).1),(fun i => (z i).2)))]
  have he := (measurePreserving_arrowProdEquivProdArrow X Y (Fin n)
    (fun _ => μ) (fun _ => ν)).integral_comp' F
  exact he.trans (integral_prod F hF)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkSiteCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ}

lemma measurable_indexedPotential (theta : X → InteractionSample p)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measurable (indexedPotential (N := N) theta) := by
  apply Measurable.of_eval
  intro σ
  apply measurable_from_prod_countable_left
  intro j
  simpa only [indexedPotential] using hθ (fun q => σ (j q))

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ClippedModelFacts
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The literal order-n replica coefficient of the three independent-label
insertions. The old spin-pattern law P and fresh-label spin-pattern law B
are arbitrary; their laws are not assumed to agree. -/
lemma replicaInsertion_combination {p n : ℕ} (M : Model p) (hM : Admissible M)
    (j : Fin p) (R : ℝ) (P B : FiniteLaw (Fin n → Spin)) :
    replicaInsertionMoment M R (fun _ : Fin p => P) -
      (p:ℝ)*replicaInsertionMoment M R (fun l : Fin p => if l=j then P else B) +
      ((p-1:ℕ):ℝ)*replicaInsertionMoment M R (fun _ : Fin p => B) =
    (∫ z : InteractionSample p,(-z.2.2.1)^n ∂M.disorder.toMeasure)*
      ((∫ z : InteractionSample p,patternFeature R P (z.2.2.2 j) ∂M.disorder.toMeasure)^p -
       (p:ℝ)*(∫ z : InteractionSample p,patternFeature R P (z.2.2.2 j) ∂M.disorder.toMeasure)*
         (∫ z : InteractionSample p,patternFeature R B (z.2.2.2 j) ∂M.disorder.toMeasure)^(p-1) +
       ((p-1:ℕ):ℝ)*(∫ z : InteractionSample p,patternFeature R B (z.2.2.2 j) ∂M.disorder.toMeasure)^p) := by
  classical
  unfold replicaInsertionMoment
  rw [upper_pattern_moment M hM j,upper_pattern_moment M hM j,upper_pattern_moment M hM j]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have he : (∏ l : Fin p, ∫ z : InteractionSample p,
      patternFeature R (if l=j then P else B) (z.2.2.2 j) ∂M.disorder.toMeasure) =
    (∫ z : InteractionSample p,patternFeature R P (z.2.2.2 j) ∂M.disorder.toMeasure)*
     (∫ z : InteractionSample p,patternFeature R B (z.2.2.2 j) ∂M.disorder.toMeasure)^(p-1) := by
    convert product_one_distinguished j
      (∫ z : InteractionSample p,patternFeature R P (z.2.2.2 j) ∂M.disorder.toMeasure)
      (∫ z : InteractionSample p,patternFeature R B (z.2.2.2 j) ∂M.disorder.toMeasure) using 1
    · apply Finset.prod_congr rfl
      intro l _
      split_ifs <;> rfl
    · simp
  rw [he]
  ring

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonCountThinning
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

lemma replicaInsertionMoment_eq {p n : ℕ} (M : Model p) (R : ℝ)
    (P : Fin p → FiniteLaw (Fin n → Spin)) :
    replicaInsertionMoment M R P =
      ∫ z : InteractionSample p,(FiniteLaw.pi P).expect
        (fun s => ∏ a : Fin n,(-z.2.2.1)*∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a)) ∂M.disorder.toMeasure := by
  unfold replicaInsertionMoment
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← FiniteLaw.expect_mul_left]
  apply FiniteLaw.expect_congr
  intro s
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma factorCut_eventually (f : Spin → ℝ) :
    ∀ᶠ R : ℕ in atTop,factorCut (R:ℝ) f=f := by
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually (eventually_ge_atTop ‖f‖)] with R hR
  simp [factorCut,hR]

lemma rawReplicaMoment_limit {p n : ℕ} (M : Model p) (hM : Admissible M)
    (P : Fin p → FiniteLaw (Fin n → Spin)) :
    Tendsto (fun R : ℕ => replicaInsertionMoment M (R:ℝ) P) atTop (𝓝 (rawReplicaMoment M P)) := by
  simp_rw [replicaInsertionMoment_eq]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
  · intro R
    apply Measurable.aestronglyMeasurable
    unfold FiniteLaw.expect
    apply Finset.measurable_sum
    intro s _
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro a _
    apply Measurable.mul (by fun_prop)
    exact Finset.measurable_prod _ (fun l _ => (measurable_pi_apply (s l a)).comp
      ((measurable_factorCut (R:ℝ)).comp (by fun_prop)))
  · exact integrable_const _
  · intro R
    filter_upwards [hM.factorization] with z hz
    rw [Real.norm_eq_abs]
    apply FiniteLaw.abs_expect_le
    intro s
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro a _
    rw [show (-z.2.2.1)*(∏ l,factorCut (R:ℝ) (z.2.2.2 l) (s l a)) =
      -(z.2.2.1*(∏ l,factorCut (R:ℝ) (z.2.2.2 l) (s l a))) by ring,abs_neg]
    exact (factorCut_product_lt_one (R:ℝ) z.2.2.1 z.2.2.2 (fun s => (hz.2 s).2) _).le
  · exact ae_of_all _ (fun z => by
      have he : ∀ᶠ R : ℕ in atTop,∀ l : Fin p,factorCut (R:ℝ) (z.2.2.2 l)=z.2.2.2 l :=
        Filter.eventually_all.mpr (fun l => factorCut_eventually (z.2.2.2 l))
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with R hR
      simp only [hR])

/-- Removing the coordinate cutoff uses only the original uniform product
bound. No additional moments of individual factors are assumed. -/
lemma rawReplica_combination_nonneg {p n : ℕ} (M : Model p) (hM : Admissible M)
    (hn : 1≤n) (j : Fin p) (P B : FiniteLaw (Fin n → Spin)) :
    0 ≤ rawReplicaMoment M (fun _ : Fin p => P) -
      (p:ℝ)*rawReplicaMoment M (fun l : Fin p => if l=j then P else B) +
      ((p-1:ℕ):ℝ)*rawReplicaMoment M (fun _ : Fin p => B) := by
  have hlim := ((rawReplicaMoment_limit M hM (fun _ : Fin p => P)).sub
    ((rawReplicaMoment_limit M hM (fun l : Fin p => if l=j then P else B)).const_mul (p:ℝ))).add
    ((rawReplicaMoment_limit M hM (fun _ : Fin p => B)).const_mul ((p-1:ℕ):ℝ))
  apply ge_of_tendsto hlim
  exact Eventually.of_forall (fun R => by
    rw [replicaInsertion_combination M hM j]
    exact mul_nonneg (hM.positivity n hn) (even_cavity_remainder_nonneg hM.even (by have := hM.arity; omega) _ _))

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma compoundPoisson_dirac_one (r : ℝ≥0) :
    compoundPoisson r (Measure.dirac (1:ℝ)) = Measure.map (fun n : ℕ => (n:ℝ)) (poissonMeasure r) := by
  rw [compoundPoisson,poissonMeasure,Measure.map_sum (measurable_of_countable _).aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul,
    Measure.map_dirac' (measurable_of_countable _)]
  congr 1
  have ha : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => Measure.dirac (1:ℝ)),∀ i,x i=1 :=
    Filter.eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => Measure.dirac (1:ℝ)) (i := i)).eventually (show ∀ᵐ x ∂Measure.dirac (1:ℝ),x=1 from by simp))
  rw [Measure.map_congr (ha.mono (fun x hx => show (∑ i,x i)=(n:ℝ) by simp [hx]))]
  simp

/-- Poisson thinning for independent uniform categorical choices. -/
lemma compoundPoisson_uniform_indicator (r : ℝ≥0) (p : ℕ) [NeZero p] :
    compoundPoisson r (Measure.map (fun a : Fin p => if a=0 then (1:ℝ) else 0)
      (finiteUniform (Fin p))) = compoundPoisson (r/p) (Measure.dirac (1:ℝ)) := by
  classical
  let : IsProbabilityMeasure (Measure.map (fun a : Fin p => if a=0 then (1:ℝ) else 0)
      (finiteUniform (Fin p))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_compoundPoisson,charFunDual_compoundPoisson]
  congr 1
  rw [charFunDual_apply,integral_map (measurable_of_countable _).aemeasurable (by fun_prop),
    integral_finiteUniform,charFunDual_apply,integral_dirac]
  have hp : (p:ℂ)≠0 := by exact_mod_cast (NeZero.ne p)
  have hs : (∑ a : Fin p,Complex.exp ((L (if a=0 then (1:ℝ) else 0):ℂ)*Complex.I)) =
      Complex.exp ((L 1:ℂ)*Complex.I)+(p-1:ℕ) := by
    have he (a : Fin p) : Complex.exp ((L (if a=0 then (1:ℝ) else 0):ℂ)*Complex.I)=
        (if a=0 then Complex.exp ((L 1:ℂ)*Complex.I)-1 else 0)+1 := by
      split_ifs <;> simp
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hpn : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]
    rw [hpn]; ring
  rw [hs]
  simp only [Fintype.card_fin,NNReal.coe_div,NNReal.coe_natCast,Complex.ofReal_div,Complex.ofReal_natCast,Complex.real_smul,Complex.ofReal_inv]
  rw [show ((p-1:ℕ):ℂ)=(p:ℂ)-1 by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]]
  field_simp
  ring

lemma map_poisson_successCount (r : ℝ≥0) (p : ℕ) [NeZero p] :
    Measure.map (fun z : (k : ℕ) × (Fin k → Fin p) => successCount z.2)
      (familyLaw (poissonMeasure r) (fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p)))) =
      poissonMeasure (r/p) := by
  classical
  have he : MeasurableEmbedding (fun n : ℕ => (n:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).measurableEmbedding Nat.cast_injective
  apply he.map_injective
  rw [Measure.map_map (measurable_of_countable _) (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCount a))),
    ← compoundPoisson_dirac_one,← compoundPoisson_uniform_indicator r p]
  simp only [Function.comp_def]
  rw [map_familyLaw_sum _ _ (fun k (a : Fin k → Fin p) => (successCount a:ℝ))
    (fun k => measurable_of_countable _)]
  unfold compoundPoisson
  congr 1
  funext k
  rw [poissonMeasure_singleton,← Measure.pi_map_pi (fun _ : Fin k => (measurable_of_countable
    (fun a : Fin p => if a=0 then (1:ℝ) else 0)).aemeasurable),
    Measure.map_map (by fun_prop) (measurable_of_countable _)]
  congr 2
  funext a
  simp [successCount]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountBridgeTools
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]
lemma integral_expect (P : FiniteLaw Ω) (μ : Measure X) (f : X → Ω → ℝ)
    (hf : ∀ i,Integrable (fun x => f x i) μ) :
    (∫ x,P.expect (f x) ∂μ)=P.expect (fun i => ∫ x,f x i ∂μ) := by
  unfold expect
  rw [integral_finsetSum _ (fun i _ => (hf i).const_mul _)]
  simp only [integral_const_mul]
end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RawPatternIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma rawReplicaMoment_eq_product {p n : ℕ} (M : Model p)
    (P : Fin p → FiniteLaw (Fin n → Spin)) :
    rawReplicaMoment M P=∫ z : InteractionSample p,(-z.2.2.1)^n*
      ∏ l : Fin p,(P l).expect (fun s => ∏ a : Fin n,z.2.2.2 l (s a)) ∂M.disorder.toMeasure := by
  unfold rawReplicaMoment
  apply integral_congr_ae
  filter_upwards [] with z
  have he (s : Fin p → Fin n → Spin) :
      (∏ a : Fin n,(-z.2.2.1)*∏ l : Fin p,z.2.2.2 l (s l a))=
        (-z.2.2.1)^n*∏ l : Fin p,∏ a : Fin n,z.2.2.2 l (s l a) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [Finset.prod_comm]
  simp_rw [he]
  rw [FiniteLaw.expect_mul_left]
  congr 1
  exact FiniteLaw.expect_pi_product P (fun l s => ∏ a : Fin n,z.2.2.2 l (s a))

lemma freshPatternFeature_raw {Z : Type} [Fintype Z] {n : ℕ}
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (f : Spin → ℝ) :
    (freshPatternLaw Q x).expect (fun s => ∏ a : Fin n,f (s a))=
      Q.expect (fun z => ∏ a : Fin n,averagedFactor f (x z a)) := by
  unfold freshPatternLaw
  rw [FiniteLaw.expect_map,FiniteLaw.expect_bind]
  apply FiniteLaw.expect_congr
  intro z
  exact FiniteLaw.expect_pi_product _ _

lemma raw_mixedPatternMoment {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (old : Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    rawReplicaMoment M (fun l : Fin p => if sel l then oldPatternLaw old else freshPatternLaw Q x) =
      ∫ z : InteractionSample p,(-z.2.2.1)^n *
        (∏ l : Fin p, if sel l then
          (FiniteLaw.uniform : FiniteLaw (Fin N)).expect (fun i => ∏ a : Fin n,z.2.2.2 l (old i a))
        else Q.expect (fun w => ∏ a : Fin n,averagedFactor (z.2.2.2 l) (x w a)))
      ∂M.disorder.toMeasure := by
  rw [rawReplicaMoment_eq_product]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  cases sel l
  · simp only [Bool.false_eq_true,↓reduceIte]
    exact freshPatternFeature_raw Q x _
  · simp only [↓reduceIte]
    exact FiniteLaw.expect_map _ _ _

/-- Averaging an inserted factor against arbitrary independent spin laws
preserves the original uniform interaction bound. -/
lemma averaged_product_bound {p : ℕ} (b : ℝ) (f : Fin p → Spin → ℝ)
    (h : ∀ s : Fin p → Spin,|b*∏ l,f l (s l)|≤1)
    (P : Fin p → FiniteLaw Spin) : |b*∏ l,(P l).expect (f l)|≤1 := by
  rw [← FiniteLaw.expect_pi_product,← FiniteLaw.expect_mul_left]
  exact FiniteLaw.abs_expect_le _ h

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionCoefficient
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma insertionCoefficient_eq_raw {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    insertionCoefficient M old Q x sel = rawReplicaMoment M
      (fun l : Fin p => if sel l then oldPatternLaw old else freshPatternLaw Q x) := by
  rw [raw_mixedPatternMoment]
  unfold insertionCoefficient
  apply integral_congr_ae
  filter_upwards [] with z
  let g := fun (l : Fin p) (w : Fin N × Z) (a : Fin n) =>
    if sel l then z.2.2.2 l (old w.1 a) else averagedFactor (z.2.2.2 l) (x w.2 a)
  have he (w : Fin p → Fin N × Z) :
      (∏ a : Fin n,-(z.2.2.1*∏ l : Fin p,g l (w l) a))=
        (-z.2.2.1)^n*∏ l : Fin p,∏ a : Fin n,g l (w l) a := by
    simp only [neg_mul_eq_neg_mul]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [Finset.prod_comm]
  change ((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)).bind (fun _ => Q))).expect
    (fun w => ∏ a : Fin n,-(z.2.2.1*∏ l : Fin p,g l (w l) a)))=_
  simp_rw [he]
  rw [FiniteLaw.expect_mul_left]
  congr 1
  rw [FiniteLaw.expect_pi_product _ (fun l w => ∏ a : Fin n,g l w a)]
  apply Finset.prod_congr rfl
  intro l _
  rw [FiniteLaw.expect_bind]
  cases h : sel l
  · simp only [g,h,Bool.false_eq_true,↓reduceIte,FiniteLaw.expect_const]
  · simp only [g,h,↓reduceIte,FiniteLaw.expect_const]

lemma insertionCoefficient_combination_nonneg {Z : Type} [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : Admissible M) (hn : 1≤n)
    (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (j : Fin p) :
    0 ≤ insertionCoefficient M old Q x (fun _ => true) -
      (p:ℝ)*insertionCoefficient M old Q x (fun l => decide (l=j)) +
      ((p-1:ℕ):ℝ)*insertionCoefficient M old Q x (fun _ => false) := by
  simp only [insertionCoefficient_eq_raw,↓reduceIte,Bool.false_eq_true,decide_eq_true_eq]
  exact rawReplica_combination_nonneg M hM hn j _ _

/-- The coefficient sign remains valid after sampling the old tilted tree;
its sampling law is common to the bond, cavity and real insertions. -/
lemma expected_insertionCoefficient_nonneg {Ω Z : Type} [Fintype Ω] [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : Admissible M) (hn : 1≤n)
    (P : FiniteLaw Ω) (old : Ω → Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (j : Fin p) :
    0 ≤ P.expect (fun w => insertionCoefficient M (old w) Q x (fun _ => true)) -
      (p:ℝ)*P.expect (fun w => insertionCoefficient M (old w) Q x (fun l => decide (l=j))) +
      ((p-1:ℕ):ℝ)*P.expect (fun w => insertionCoefficient M (old w) Q x (fun _ => false)) := by
  rw [← FiniteLaw.expect_mul_left,← FiniteLaw.expect_sub,← FiniteLaw.expect_mul_left,
    ← FiniteLaw.expect_add]
  exact P.expect_nonneg (fun w => insertionCoefficient_combination_nonneg M hM hn (old w) Q x j)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionPoint
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι α β : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

lemma expect_pi_bind (P : ι → FiniteLaw α) (Q : ι → α → FiniteLaw β)
    (f : (ι → α×β) → ℝ) :
    (pi (fun i => (P i).bind (Q i))).expect f =
      (pi P).expect (fun a => (pi (fun i => Q i (a i))).expect (fun b => f (fun i => (a i,b i)))) := by
  classical
  let e : (ι → α×β) ≃ (ι → α)×(ι → β) :=
    ⟨fun x => (fun i => (x i).1,fun i => (x i).2),fun x i => (x.1 i,x.2 i),
      fun x => rfl,fun x => rfl⟩
  unfold expect
  rw [show (∑ x, (pi (fun i => (P i).bind (Q i))).weight x*f x)=
      ∑ x : (ι → α)×(ι → β),(∏ i,(P i).weight (x.1 i))*(∏ i,(Q i (x.1 i)).weight (x.2 i))*f (fun i => (x.1 i,x.2 i)) from
    Fintype.sum_equiv e _ _ (fun x => by
      simp only [e,Equiv.coe_fn_mk,pi,bind,Finset.prod_mul_distrib])]
  simp only [Fintype.sum_prod_type,pi,Finset.mul_sum,mul_assoc]

end DilutedSpinGlass.FiniteLaw

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

lemma mixedFactor_bound {p : ℕ} (z : InteractionSample p)
    (hz : ∀ s : Fin p → Spin,|z.2.2.1*∏ l,z.2.2.2 l (s l)|≤1)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) : |mixedFactor z sel s x|≤1 := by
  have he (l : Fin p) :
      ((if sel l then FiniteLaw.point (s l) else qLaw (x l)) : FiniteLaw Spin).expect (z.2.2.2 l)=
      if sel l then z.2.2.2 l (s l) else averagedFactor (z.2.2.2 l) (x l) := by
    cases sel l <;> simp only [Bool.false_eq_true,↓reduceIte,FiniteLaw.expect_point]
    rfl
  have hh := averaged_product_bound z.2.2.1 z.2.2.2 hz
    (fun l => if sel l then FiniteLaw.point (s l) else qLaw (x l))
  simpa only [he,mixedFactor] using hh

lemma measurable_mixedFactor {p : ℕ} (sel : Fin p → Bool)
    (s : Fin p → Spin) (x : Fin p → ℝ) : Measurable (fun z : InteractionSample p => mixedFactor z sel s x) := by
  unfold mixedFactor averagedFactor
  apply Measurable.mul (by fun_prop)
  apply Finset.measurable_prod
  intro l _
  cases sel l <;> simp only [Bool.false_eq_true,↓reduceIte]
  · apply Finset.measurable_sum
    intro a _
    fun_prop
  · fun_prop

lemma measurable_insertionPoint {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    Measurable (fun z : InteractionSample p => insertionPoint z old Q x sel) := by
  unfold insertionPoint FiniteLaw.expect
  apply Finset.measurable_sum
  intro w _
  apply Measurable.const_mul
  exact Finset.measurable_prod _ (fun a _ => (measurable_mixedFactor sel _ _).neg)

lemma insertionPoint_bound {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (z : InteractionSample p) (hz : ∀ s : Fin p → Spin,|z.2.2.1*∏ l,z.2.2.2 l (s l)|≤1)
    (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    |insertionPoint z old Q x sel|≤1 := by
  apply FiniteLaw.abs_expect_le
  intro w
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro a _
  rw [abs_neg]
  exact mixedFactor_bound z hz sel _ _

lemma integrable_insertionPoint {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (hM : Admissible M) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    Integrable (fun z => insertionPoint z old Q x sel) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_insertionPoint old Q x sel).aestronglyMeasurable 1
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using insertionPoint_bound z (fun s => (hz.2 s).2.le) old Q x sel

lemma integral_expected_insertionPoint {Ω Z : Type} [Fintype Ω] [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : Admissible M)
    (P : FiniteLaw Ω) (old : Ω → Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    (∫ z,P.expect (fun w => insertionPoint z (old w) Q x sel) ∂M.disorder.toMeasure)=
      P.expect (fun w => insertionCoefficient M (old w) Q x sel) :=
  FiniteLaw.integral_expect P M.disorder.toMeasure _
    (fun w => integrable_insertionPoint M hM (old w) Q x sel)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularizedNormalization
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

lemma regularized_ratio_bound {B d e t : ℝ} (hB : 0 ≤ B) (hd : |d|<1)
    (ht0 : 0 ≤ t) (ht : t<1)
    (hl : Real.exp (-B)*(1+d)≤1+e) (hu : 1+e≤Real.exp B*(1+d)) :
    |Real.log ((1+t*e)/(1+t*d))|≤B := by
  have hd' : -1<d := (abs_lt.mp hd).1
  have hden : 0<1+t*d := by nlinarith
  have hexpl : Real.exp (-B)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hB)
  have hexpu : 1≤Real.exp B := Real.one_le_exp_iff.mpr hB
  have htl : Real.exp (-B)*(1+t*d)≤1+t*e := by
    have hh := mul_nonneg (sub_nonneg.mpr hexpl) (sub_nonneg.mpr ht.le)
    nlinarith [mul_le_mul_of_nonneg_left hl ht0]
  have htu : 1+t*e≤Real.exp B*(1+t*d) := by
    have hh := mul_nonneg (sub_nonneg.mpr hexpu) (sub_nonneg.mpr ht.le)
    nlinarith [mul_le_mul_of_nonneg_left hu ht0]
  have hlow : Real.exp (-B)≤(1+t*e)/(1+t*d) := (le_div_iff₀ hden).mpr htl
  have hupp : (1+t*e)/(1+t*d)≤Real.exp B := (div_le_iff₀ hden).mpr htu
  have hr : 0<(1+t*e)/(1+t*d) := (Real.exp_pos _).trans_le hlow
  apply abs_le.mpr
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-B)) hlow
  · simpa only [Real.log_exp] using Real.log_le_log hr hupp

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

lemma factor_expect (P : FiniteLaw Ω) (θ D : Ω → ℝ) (a : ℝ)
    (hfac : ∀ s,Real.exp (θ s)=a*(1+D s)) :
    P.expect (fun s => Real.exp (θ s))=a*(1+P.expect D) := by
  simp_rw [hfac]
  rw [expect_mul_left,expect_add,expect_const]

lemma normalized_factor_bounds (P : FiniteLaw Ω) (θ D : Ω → ℝ) (a : ℝ)
    (ha : 0<a) (hfac : ∀ s,Real.exp (θ s)=a*(1+D s))
    (s₀ : Ω) {B : ℝ} (hθ : ∀ s,|θ s|≤B) :
    Real.exp (-2*B)*(1+D s₀)≤1+P.expect D ∧
      1+P.expect D≤Real.exp (2*B)*(1+D s₀) := by
  have hl : P.expect (fun _ => Real.exp (-2*B)*Real.exp (θ s₀))≤
      P.expect (fun s => Real.exp (θ s)) := by
    apply P.expect_mono
    intro s
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := abs_le.mp (hθ s)
    have h2 := abs_le.mp (hθ s₀)
    linarith
  have hu : P.expect (fun s => Real.exp (θ s))≤
      P.expect (fun _ => Real.exp (2*B)*Real.exp (θ s₀)) := by
    apply P.expect_mono
    intro s
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := abs_le.mp (hθ s)
    have h2 := abs_le.mp (hθ s₀)
    linarith
  rw [expect_const,factor_expect P θ D a hfac,hfac s₀] at hl
  rw [expect_const,factor_expect P θ D a hfac,hfac s₀] at hu
  constructor
  · apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith only [hl]
  · apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith only [hu]

lemma normalized_factor_log_bound (P : FiniteLaw Ω) (θ D : Ω → ℝ) (a : ℝ)
    (ha : 0<a) (hfac : ∀ s,Real.exp (θ s)=a*(1+D s))
    (s₀ : Ω) (hD : |D s₀|<1) {B t : ℝ} (hB : 0 ≤ B)
    (hθ : ∀ s,|θ s|≤B) (ht0 : 0 ≤ t) (ht : t<1) :
    |Real.log ((1+t*P.expect D)/(1+t*D s₀))|≤2*B := by
  have hh := normalized_factor_bounds P θ D a ha hfac s₀ hθ
  exact regularized_ratio_bound (by positivity) hD ht0 ht
    (by simpa only [neg_mul] using hh.1) hh.2

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TowerPadding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma logMean_bind_add (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ)
    (f : Ω → ℝ) (g : Λ → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1+g z.2)=P.logMean m f+Q.logMean m g := by
  unfold logMean expMoment
  simp only [mul_add,Real.exp_add,expect_bind,expect_mul_left,expect_mul_right]
  change Real.log (P.expMoment m f*Q.expMoment m g)/m=Real.log (P.expMoment m f)/m+Real.log (Q.expMoment m g)/m
  rw [Real.log_mul (P.expMoment_pos m f).ne' (Q.expMoment_pos m g).ne',add_div]

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma backwardLog_prod_add (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) (g : FinitePath Λ n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)+g (pathSnd n y))=
      backwardLog n T m f+backwardLog n U m g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change FiniteLaw Ω×(Ω → KernelTower Ω n) at T
      change FiniteLaw Λ×(Λ → KernelTower Λ n) at U
      change Ω×FinitePath Ω n → ℝ at f
      change Λ×FinitePath Λ n → ℝ at g
      simp only [backwardLog,prod,pathFst,pathSnd]
      have hh (x : Ω×Λ) := ih (T.2 x.1) (U.2 x.2) (fun j => m j.succ)
        (fun y => f (x.1,y)) (fun y => g (x.2,y))
      simp only [hh]
      exact FiniteLaw.logMean_bind_add T.1 U.1 (m 0)
        (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
        (fun x => backwardLog n (U.2 x) (fun j => m j.succ) (fun y => g (x,y)))

lemma backwardLog_pad (a : Ω) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : m (Fin.last n)≠0) (f : FinitePath Ω n → ℝ) :
    backwardLog (n+1) (pad a n T) m (fun y => f (pathPrefix n y))=
      backwardLog n T (fun j => m j.castSucc) f := by
  induction n with
  | zero =>
      change (FiniteLaw.point a).logMean (m 0) (fun _ => f ())=f ()
      exact FiniteLaw.logMean_const _ hm _
  | succ n ih =>
      simp only [pad,backwardLog,pathPrefix]
      congr 1
      funext x
      exact ih (T.2 x) (fun j => m j.succ) hm (fun y => f (x,y))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TowerSum
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace FiniteLaw
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i,Fintype (A i)]
lemma logMean_pi_sum (Q : (i : ι) → FiniteLaw (A i)) (m : ℝ)
    (f : (i : ι) → A i → ℝ) :
    (pi Q).logMean m (fun x => ∑ i,f i (x i))=∑ i,(Q i).logMean m (f i) := by
  classical
  unfold logMean expMoment
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [expect_pi_product Q (fun i x => Real.exp (m*f i x)),Real.log_prod]
  · simp only [Finset.sum_div]
  · intro i _
    exact (expMoment_pos (Q i) m (f i)).ne'
end FiniteLaw

namespace KernelTower
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [Fintype A]
lemma backwardLog_pi_sum (n : ℕ) (T : (i : ι) → KernelTower A n)
    (m : Fin n → ℝ) (f : (i : ι) → FinitePath A n → ℝ) :
    backwardLog n (pi n T) m (fun y => ∑ i,f i (FinitePath.proj n y i))=
      ∑ i,backwardLog n (T i) m (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ι → FiniteLaw A × (A → KernelTower A n) at T
    change ι → A × FinitePath A n → ℝ at f
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun x => backwardLog n (pi n (fun i => (T i).2 (x i))) (fun j => m j.succ)
        (fun y => ∑ i,f i (x i,FinitePath.proj n y i))) =
      ∑ i,(T i).1.logMean (m 0) (fun a => backwardLog n ((T i).2 a) (fun j => m j.succ) (fun y => f i (a,y)))
    have he : (fun x : ι → A => backwardLog n (pi n (fun i => (T i).2 (x i))) (fun j => m j.succ)
        (fun y => ∑ i,f i (x i,FinitePath.proj n y i))) =
      (fun x => ∑ i,backwardLog n ((T i).2 (x i)) (fun j => m j.succ) (fun y => f i (x i,y))) := by
      funext x
      exact ih (fun i => (T i).2 (x i)) (fun j => m j.succ) (fun i y => f i (x i,y))
    rw [he]
    exact FiniteLaw.logMean_pi_sum (fun i => (T i).1) (m 0)
      (fun i x => backwardLog n ((T i).2 x) (fun j => m j.succ) (fun y => f i (x,y)))
end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CommonTreeSample
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
namespace KernelTower
variable {Ω Λ Ω' Λ' : Type} [Fintype Ω] [Fintype Λ] [Fintype Ω'] [Fintype Λ']

lemma Projects.refl (n : ℕ) (T : KernelTower Ω n) : Projects id n T T := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨fun _ => rfl,fun a => ih (T.2 a)⟩

lemma Projects.comp {π : Ω → Λ} {ρ : Λ → Ω'} (n : ℕ)
    {T : KernelTower Ω n} {U : KernelTower Λ n} {V : KernelTower Ω' n}
    (h : Projects π n T U) (g : Projects ρ n U V) : Projects (ρ ∘ π) n T V := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (h.2 a) (g.2 (π a))⟩
    intro f
    exact (h.1 (f ∘ ρ)).trans (g.1 f)

lemma Projects.prod {π : Ω → Ω'} {ρ : Λ → Λ'} (n : ℕ)
    {T : KernelTower Ω n} {T' : KernelTower Ω' n}
    {U : KernelTower Λ n} {U' : KernelTower Λ' n}
    (h : Projects π n T T') (g : Projects ρ n U U') :
    Projects (fun z : Ω×Λ => (π z.1,ρ z.2)) n (prod n T U) (prod n T' U') := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (h.2 a.1) (g.2 a.2)⟩
    intro f
    change (T.1.bind (fun _ => U.1)).expect (fun z => f (π z.1,ρ z.2)) =
      (T'.1.bind (fun _ => U'.1)).expect f
    rw [FiniteLaw.expect_bind,FiniteLaw.expect_bind]
    have he : (fun a => U.1.expect (fun b => f (π a,ρ b)))=
        (fun a => U'.1.expect (fun b => f (π a,b))) := by
      funext a
      exact g.1 (fun b => f (π a,b))
    rw [he]
    exact h.1 (fun a => U'.1.expect (fun b => f (a,b)))

lemma pi_prod_projects {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (T : ι → KernelTower Ω n) (U : ι → KernelTower Λ n) (c : ι) :
    Projects (fun z : ι → Ω×Λ => (fun i => (z i).1,(z c).2)) n
      (pi n (fun i => prod n (T i) (U i))) (prod n (pi n T) (U c)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (fun i => (T i).2 (a i).1) (fun i => (U i).2 (a i).2)⟩
    intro f
    change (FiniteLaw.pi (fun i => (T i).1.bind (fun _ => (U i).1))).expect
      (fun z => f (fun i => (z i).1,(z c).2)) =
      ((FiniteLaw.pi (fun i => (T i).1)).bind (fun _ => (U c).1)).expect f
    rw [FiniteLaw.expect_pi_bind]
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact FiniteLaw.expect_pi_marginal (fun i => (U i).1) c (fun b => f (a,b))

omit [Fintype Ω] [Fintype Λ] [Fintype Ω'] in
lemma pathMap_comp (π : Ω → Λ) (ρ : Λ → Ω') (n : ℕ) (y : FinitePath Ω n) :
    pathMap (ρ ∘ π) n y=pathMap ρ n (pathMap π n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

end KernelTower
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω Λ R ι : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [Fintype ι] [DecidableEq ι] {n : ℕ}

lemma prod_pi_sample_expect (S : PrescribedTree n) (T : KernelTower Ω n)
    (U : ι → KernelTower Λ n) (g : (ι → Sample Λ S) → Sample Ω S → ℝ) :
    (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n U))).expect
      (fun w => g (fun j => sampleMap (fun x : ι → Λ => x j) S (sampleSnd S w))
        (sampleFst S w)) =
    (S.sampleLaw T).expect (fun old =>
      (FiniteLaw.pi (fun j => S.sampleLaw (U j))).expect (fun fresh => g fresh old)) := by
  rw [sampleExpect_prod]
  apply FiniteLaw.expect_congr
  intro old
  rw [sampleExpect_piTower]
  apply FiniteLaw.expect_congr
  intro a
  simp only [sampleFst_pair,sampleSnd_pair,sampleMap_pi]

/-- Each new label is independently sampled, including its root, on the same
prescribed replica tree as the old system. -/
lemma common_sample_expect (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (g : (ι → R×Sample Λ S) → Sample Ω S → ℝ) :
    (FiniteLaw.pi (fun _ : ι => Q)).expect (fun r =>
      (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n (fun j : ι => U (r j))))).expect
        (fun w => g (fun j => (r j,sampleMap (fun x : ι → Λ => x j) S (sampleSnd S w)))
          (sampleFst S w))) =
    (S.sampleLaw T).expect (fun old =>
      (FiniteLaw.pi (fun _ : ι => Q.bind (fun r => S.sampleLaw (U r)))).expect
        (fun fresh => g fresh old)) := by
  let H (r : ι → R) (old : Sample Ω S) :=
    (FiniteLaw.pi (fun j : ι => S.sampleLaw (U (r j)))).expect
      (fun a => g (fun j => (r j,a j)) old)
  calc
    _ = (FiniteLaw.pi (fun _ : ι => Q)).expect (fun r => (S.sampleLaw T).expect (H r)) := by
      apply FiniteLaw.expect_congr
      intro r
      exact prod_pi_sample_expect S T (fun j => U (r j))
        (fun a old => g (fun j => (r j,a j)) old)
    _ = (S.sampleLaw T).expect (fun old => (FiniteLaw.pi (fun _ : ι => Q)).expect (fun r => H r old)) :=
      FiniteLaw.expect_comm _ _ _
    _ = _ := by
      apply FiniteLaw.expect_congr
      intro old
      exact (FiniteLaw.expect_pi_bind (fun _ : ι => Q) (fun _ r => S.sampleLaw (U r))
        (fun fresh => g fresh old)).symm

omit [Fintype Ω] in
lemma leafProduct_eq_fin_prod (S : PrescribedTree n) (D : FinitePath Ω n → ℝ)
    (w : Sample Ω S) :
    leafProduct S D w=∏ a : Fin (Fintype.card S.Leaf),D (S.pathAt ((Fintype.equivFin S.Leaf).symm a) w) := by
  rw [leafProduct_eq_prod]
  exact Fintype.prod_equiv (Fintype.equivFin S.Leaf) _ _ (fun a => by simp)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma mixedTree_leafProduct {p N : ℕ} (S : PrescribedTree n)
    (z : InteractionSample p) (sel : Fin p → Bool)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (r : Fin p → R) (i : Fin p → Fin N) (w : Sample (Ω × (Fin p → Λ)) S) :
    leafProduct S (fun y => -mixedTreeD z sel V x r i y) w=
      ∏ a : Fin (Fintype.card S.Leaf),-mixedFactor z sel
        (fun l => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) (sampleFst S w)) (i l))
        (fun l => x (r l) (S.pathAt ((Fintype.equivFin S.Leaf).symm a)
          (sampleMap (fun a : Fin p → Λ => a l) S (sampleSnd S w)))) := by
  rw [leafProduct_eq_fin_prod]
  simp only [mixedTreeD,pathAt_sampleMap,pathAt_sampleFst,pathAt_sampleSnd]

lemma common_tree_sample {p N : ℕ} [NeZero N] (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) (i : Fin p → Fin N) :
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))).expect
        (leafProduct S (fun y => -mixedTreeD z sel V x r i y))) =
    (S.sampleLaw T).expect (fun old =>
      (FiniteLaw.pi (fun _ : Fin p => Q.bind (fun r => S.sampleLaw (U r)))).expect
        (fun fresh => ∏ a : Fin (Fintype.card S.Leaf),-mixedFactor z sel
          (fun l => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) (i l))
          (fun l => x (fresh l).1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) (fresh l).2)))) := by
  rw [← common_sample_expect]
  apply FiniteLaw.expect_congr
  intro r
  apply FiniteLaw.expect_congr
  intro w
  exact mixedTree_leafProduct S z sel V x r i w

lemma common_tree_point {p N : ℕ} [NeZero N] (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) :
    (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
      (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
        (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))).expect
          (leafProduct S (fun y => -mixedTreeD z sel V x r i y)))) =
    (S.sampleLaw T).expect (fun old => insertionPoint z
      (fun i a => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) i)
      (Q.bind (fun r => S.sampleLaw (U r)))
      (fun w a => x w.1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) w.2)) sel) := by
  let F (i : Fin p → Fin N) (old : Sample Ω S) :=
    (FiniteLaw.pi (fun _ : Fin p => Q.bind (fun r => S.sampleLaw (U r)))).expect
      (fun fresh => ∏ a : Fin (Fintype.card S.Leaf),-mixedFactor z sel
        (fun l => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) (i l))
        (fun l => x (fresh l).1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) (fresh l).2)))
  calc
    _ = (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
        (fun i => (S.sampleLaw T).expect (F i)) := by
      apply FiniteLaw.expect_congr
      intro i
      exact common_tree_sample S T Q U V x z sel i
    _ = (S.sampleLaw T).expect (fun old =>
        (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
          (fun i => F i old)) := FiniteLaw.expect_comm _ _ _
    _ = _ := by
      apply FiniteLaw.expect_congr
      intro old
      exact (FiniteLaw.expect_pi_bind
        (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))
        (fun _ _ => Q.bind (fun r => S.sampleLaw (U r)))
        (fun w => ∏ a : Fin (Fintype.card S.Leaf),-mixedFactor z sel
          (fun l => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) (w l).1)
          (fun l => x (w l).2.1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) (w l).2.2)))).symm

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperCommonCoefficient
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

lemma measurable_mixedLeafAvg (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (sel : Fin p → Bool) : Measurable (fun z => mixedLeafAvg S T Q U V x z sel) := by
  unfold mixedLeafAvg
  simp_rw [common_tree_point]
  exact FiniteLaw.measurable_expect _ (fun old => measurable_insertionPoint _ _ _ _)

lemma mixedLeafAvg_bound (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (z : InteractionSample p) (hz : ∀ s : Fin p → Spin,|z.2.2.1*∏ l,z.2.2.2 l (s l)|≤1)
    (sel : Fin p → Bool) : |mixedLeafAvg S T Q U V x z sel|≤1 := by
  rw [mixedLeafAvg,common_tree_point]
  exact FiniteLaw.abs_expect_le _ (fun old => insertionPoint_bound z hz _ _ _ _)

lemma integrable_mixedLeafAvg (M : Model p) (hM : Admissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (sel : Fin p → Bool) : Integrable (fun z => mixedLeafAvg S T Q U V x z sel) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_mixedLeafAvg S T Q U V x sel).aestronglyMeasurable 1
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using mixedLeafAvg_bound S T Q U V x z (fun s => (hz.2 s).2.le) sel

lemma integratedMixedLeaf_identity (M : Model p) (hM : Admissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (sel : Fin p → Bool) :
    (∫ z,mixedLeafAvg S T Q U V x z sel ∂M.disorder.toMeasure)=
    (S.sampleLaw T).expect (fun old => insertionCoefficient M
      (fun i a => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) i)
      (Q.bind (fun r => S.sampleLaw (U r)))
      (fun w a => x w.1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) w.2)) sel) := by
  unfold mixedLeafAvg
  simp_rw [common_tree_point]
  exact integral_expected_insertionPoint M hM _ _ _ _ _

lemma integratedMixedLeaf_combination_nonneg (M : Model p) (hM : Admissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    0 ≤ (∫ z,mixedLeafAvg S T Q U V x z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedLeafAvg S T Q U V x z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedLeafAvg S T Q U V x z (fun _ => false) ∂M.disorder.toMeasure) := by
  simp only [integratedMixedLeaf_identity M hM]
  apply expected_insertionCoefficient_nonneg M hM
  rw [card_leaf]
  exact leaves_pos S

lemma qExpect_expect {A : Type} [Fintype A] (P : FiniteLaw A)
    (m : Fin (n+1) → ℝ) (F : A → PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun S => P.expect (fun a => F a S)) k S =
      P.expect (fun a => qExpect m (F a) k S) := by
  unfold FiniteLaw.expect
  rw [qExpect_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [mul_comm (P.weight a)] using qExpect_mul_const m (F a) (P.weight a) k S

lemma qExpect_linear_combination (m : Fin (n+1) → ℝ)
    (F G H : PrescribedTree n → ℝ) (a b : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun S => F S-a*G S+b*H S) k S =
      qExpect m F k S-a*qExpect m G k S+b*qExpect m H k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect,ih,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    congr 1
    · congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring

lemma mixedQMoment_combination_nonneg (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (k : ℕ) (S : PrescribedTree n) (j : Fin p) :
    0 ≤ qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun _ => true) ∂M.disorder.toMeasure) k S-
      (p:ℝ)*qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun l => decide (l=j)) ∂M.disorder.toMeasure) k S+
      ((p-1:ℕ):ℝ)*qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun _ => false) ∂M.disorder.toMeasure) k S := by
  rw [← qExpect_linear_combination]
  exact qExpect_nonneg m hm hpos _ (fun S => integratedMixedLeaf_combination_nonneg M hM S T Q U V x j) k S

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperRegularized
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

lemma mixedQMoment_eq (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (z : InteractionSample p) (sel : Fin p → Bool) (k : ℕ) :
    qExpect m (fun S => mixedLeafAvg S T Q U V x z sel) k (single n) =
      (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
        (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
          qMoment m (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))
            (fun y => -mixedTreeD z sel V x r i y) k (single n))) := by
  unfold mixedLeafAvg
  rw [qExpect_expect]
  apply FiniteLaw.expect_congr
  intro i
  rw [qExpect_expect]
  rfl

lemma mixedLogAvg_negative_tail (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (z : InteractionSample p) (hz : ∀ s : Fin p → Spin,|z.2.2.1*∏ l,z.2.2.2 l (s l)|≤1)
    (sel : Fin p → Bool) {t : ℝ} (ht : |t|<1) (K : ℕ) :
    |mixedLogAvg T Q U V x m z sel t-∑ k∈Finset.range K,
      -(t^(k+1)/(k+1))*qExpect m (fun S => mixedLeafAvg S T Q U V x z sel) k (single n)| ≤
        ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
  simp only [mixedLogAvg,mixedQMoment_eq]
  simp_rw [← FiniteLaw.expect_mul_left,← FiniteLaw.expect_sum,← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le
  intro i
  apply FiniteLaw.abs_expect_le
  intro r
  exact logInsertion_negative_tail _ m hm hpos hnz hroot hend _
    (fun y => mixedFactor_bound z hz sel _ _) ht K

lemma measurable_mixedLogAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (sel : Fin p → Bool) (t : ℝ) :
    Measurable (fun z => mixedLogAvg T Q U V x m z sel t) := by
  apply FiniteLaw.measurable_expect
  intro i
  apply FiniteLaw.measurable_expect
  intro r
  apply KernelTower.measurable_backwardLog
  intro y
  exact ((measurable_mixedFactor sel _ _).const_mul t |>.const_add 1).log

lemma integrable_mixedLogAvg (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (sel : Fin p → Bool) {t : ℝ} (ht : |t|<1) :
    Integrable (fun z => mixedLogAvg T Q U V x m z sel t) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_mixedLogAvg T Q U V x m sel t).aestronglyMeasurable
    (∑' k : ℕ,|t|^(k+1)/(k+1))
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs,Finset.range_zero,Finset.sum_empty,sub_zero,Nat.add_zero,
    Nat.cast_zero,add_zero] using mixedLogAvg_negative_tail T Q U V x m hm hpos hnz hroot hend
      z (fun s => (hz.2 s).2.le) sel ht 0

lemma integral_mixedLogAvg_negative_tail (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (sel : Fin p → Bool) {t : ℝ} (ht : |t|<1) (K : ℕ) :
    |(∫ z,mixedLogAvg T Q U V x m z sel t ∂M.disorder.toMeasure)-∑ k∈Finset.range K,
      -(t^(k+1)/(k+1))*qExpect m
        (fun S => ∫ z,mixedLeafAvg S T Q U V x z sel ∂M.disorder.toMeasure) k (single n)| ≤
        ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
  have hi (S : PrescribedTree n) := integrable_mixedLeafAvg M hM S T Q U V x sel
  simp_rw [← integral_qExpect _ m _ hi,← integral_const_mul]
  rw [← integral_finsetSum _ (fun k _ => (integrable_qExpect _ m _ hi k (single n)).const_mul _)]
  rw [← integral_sub (integrable_mixedLogAvg M hM T Q U V x m hm hpos hnz hroot hend sel ht)
    (integrable_finsetSum _ (fun k _ => (integrable_qExpect _ m _ hi k (single n)).const_mul _))]
  have hb : ∀ᵐ z ∂M.disorder.toMeasure,
      ‖mixedLogAvg T Q U V x m z sel t-∑ k∈Finset.range K,
        -(t^(k+1)/(k+1))*qExpect m (fun S => mixedLeafAvg S T Q U V x z sel) k (single n)‖ ≤
          ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
    filter_upwards [hM.factorization] with z hz
    simpa only [Real.norm_eq_abs] using mixedLogAvg_negative_tail T Q U V x m hm hpos hnz hroot hend
      z (fun s => (hz.2 s).2.le) sel ht K
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

lemma negative_series_combination {A B C a b t R : ℝ} (ha : 0≤a) (hb : 0≤b)
    (ht : 0≤t) (f g h : ℕ → ℝ) (K : ℕ)
    (hA : |A-∑ k∈Finset.range K,-(t^(k+1)/(k+1))*f k|≤R)
    (hB : |B-∑ k∈Finset.range K,-(t^(k+1)/(k+1))*g k|≤R)
    (hC : |C-∑ k∈Finset.range K,-(t^(k+1)/(k+1))*h k|≤R)
    (hc : ∀ k, 0≤f k-a*g k+b*h k) : A-a*B+b*C≤(1+a+b)*R := by
  have hs : (∑ k∈Finset.range K,-(t^(k+1)/(k+1))*f k)-
      a*(∑ k∈Finset.range K,-(t^(k+1)/(k+1))*g k)+
      b*(∑ k∈Finset.range K,-(t^(k+1)/(k+1))*h k) ≤0 := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_nonpos
    intro k _
    have he : -(t^(k+1)/(k+1))*f k-a*(-(t^(k+1)/(k+1))*g k)+
        b*(-(t^(k+1)/(k+1))*h k)=-(t^(k+1)/(k+1))*(f k-a*g k+b*h k) := by ring
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (pow_nonneg ht _) (by positivity))) (hc k)
  have hA' := (abs_le.mp hA).2
  have hB' := mul_le_mul_of_nonneg_left (abs_le.mp hB).1 ha
  have hC' := mul_le_mul_of_nonneg_left (abs_le.mp hC).2 hb
  nlinarith only [hs,hA',hB',hC']

/-- The common-tree regularized interpolation derivative has the required
sign under the original factorization and positivity hypotheses. -/
lemma integral_mixedLog_combination_nonpos (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    (∫ z,mixedLogAvg T Q U V x m z (fun _ => true) t ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedLogAvg T Q U V x m z (fun l => decide (l=j)) t ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedLogAvg T Q U V x m z (fun _ => false) t ∂M.disorder.toMeasure) ≤0 := by
  have ht' : |t|<1 := by rwa [abs_of_nonneg ht0]
  have hlim : Tendsto (fun K : ℕ => (1+(p:ℝ)+((p-1:ℕ):ℝ))*
      ∑' k : ℕ,|t|^(k+K+1)/(k+K+1)) atTop (𝓝 0) := by
    convert (tendsto_sum_nat_add (fun k : ℕ => |t|^(k+1)/(k+1))).const_mul
      (1+(p:ℝ)+((p-1:ℕ):ℝ)) using 1 <;> simp
  apply ge_of_tendsto hlim
  exact Eventually.of_forall (fun K => negative_series_combination (Nat.cast_nonneg p)
    (Nat.cast_nonneg (p-1)) ht0 _ _ _ K
    (integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (fun k => mixedQMoment_combination_nonneg M hM T Q U V x m hm hpos k (single n) j))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_NormalizedInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology

namespace FiniteLaw
variable {A : Type} [Fintype A]

lemma tendsto_expect {X : Type} {l : Filter X} (P : FiniteLaw A)
    (f : X → A → ℝ) (g : A → ℝ) (hf : ∀ a,Tendsto (fun x => f x a) l (𝓝 (g a))) :
    Tendsto (fun x => P.expect (f x)) l (𝓝 (P.expect g)) := by
  unfold expect
  exact tendsto_finsetSum _ (fun a _ => (hf a).const_mul _)

lemma tendsto_logMean {X : Type} {l : Filter X} (P : FiniteLaw A) (m : ℝ)
    (f : X → A → ℝ) (g : A → ℝ) (hf : ∀ a,Tendsto (fun x => f x a) l (𝓝 (g a))) :
    Tendsto (fun x => P.logMean m (f x)) l (𝓝 (P.logMean m g)) := by
  have he := P.tendsto_expect (fun x a => Real.exp (m*f x a)) (fun a => Real.exp (m*g a))
    (fun a => ((hf a).const_mul m).rexp)
  exact (he.log (ne_of_gt (P.expMoment_pos m g))).div_const m

end FiniteLaw
namespace KernelTower
variable {Ω : Type} [Fintype Ω]

lemma tendsto_backwardLog {X : Type} {l : Filter X} (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : X → FinitePath Ω n → ℝ) (g : FinitePath Ω n → ℝ)
    (hf : ∀ a,Tendsto (fun x => f x a) l (𝓝 (g a))) :
    Tendsto (fun x => backwardLog n T m (f x)) l (𝓝 (backwardLog n T m g)) := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
      exact T.1.tendsto_logMean (m 0) _ _ (fun a => ih (T.2 a) (fun j => m j.succ)
        (fun x y => f x (a,y)) (fun y => g (a,y)) (fun y => hf (a,y)))

end KernelTower
namespace PrescribedTree
variable {Ω A : Type} [Fintype Ω] [Fintype A] {n : ℕ}

lemma normalized_logInsertion_eq (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n,m j.succ≠0) (D : FinitePath Ω n → ℝ) (d t : ℝ)
    (hd : 0<1+t*d) (hD : ∀ y,0<1+t*D y) :
    logInsertion T m D t-Real.log (1+t*d)=
      KernelTower.backwardLog n T (fun j => m j.succ)
        (fun y => Real.log ((1+t*D y)/(1+t*d))) := by
  simp_rw [Real.log_div (ne_of_gt (hD _)) (ne_of_gt hd),sub_eq_add_neg]
  exact (KernelTower.backwardLog_add n T _ hnz _ _).symm

lemma normalized_logInsertion_bound (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n,0 < m j.succ) (P : FinitePath Ω n → FiniteLaw A)
    (θ D : A → ℝ) (a : ℝ) (ha : 0<a) (hfac : ∀ s,Real.exp (θ s)=a*(1+D s))
    (s₀ : A) (hD : ∀ s,|D s|<1) {B t : ℝ} (hB : 0≤B) (hθ : ∀ s,|θ s|≤B)
    (ht0 : 0≤t) (ht : t<1) :
    |logInsertion T m (fun y => (P y).expect D) t-Real.log (1+t*D s₀)|≤2*B := by
  have ht' : |t|<1 := by rwa [abs_of_nonneg ht0]
  have hDP (y : FinitePath Ω n) : |(P y).expect D|≤1 :=
    (P y).abs_expect_le (fun a => (hD a).le)
  rw [normalized_logInsertion_eq T m (fun j => ne_of_gt (hm j)) _ _ _
    (insertion_pos (n := 0) (Ω := Unit) (fun _ => D s₀) (fun _ => (hD s₀).le) ht' ())
    (fun y => insertion_pos _ hDP ht' y)]
  exact KernelTower.backwardLog_bound n T _ hm (fun y =>
    (P y).normalized_factor_log_bound θ D a ha hfac s₀ (hD s₀) hB hθ ht0 ht)

lemma normalized_logInsertion_limit (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n,m j.succ≠0) (P : FinitePath Ω n → FiniteLaw A)
    (θ D : A → ℝ) (a : ℝ) (ha : 0<a) (hfac : ∀ s,Real.exp (θ s)=a*(1+D s))
    (s₀ : A) (hD : ∀ s,|D s|<1) :
    Tendsto (fun t : ℝ => logInsertion T m (fun y => (P y).expect D) t-Real.log (1+t*D s₀))
      (𝓝 1) (𝓝 (KernelTower.backwardLog n T (fun j => m j.succ)
        (fun y => (P y).logMean 1 θ)-θ s₀)) := by
  have hDP (y : FinitePath Ω n) : 0<1+(P y).expect D := by
    have hh := (P y).factor_expect θ D a hfac
    have hp := (P y).expMoment_pos 1 θ
    simp only [FiniteLaw.expMoment,one_mul] at hp
    nlinarith
  have hd : 0<1+D s₀ := by have := (abs_lt.mp (hD s₀)).1; linarith
  have hlog (y : FinitePath Ω n) :
      (P y).logMean 1 θ=Real.log (1+(P y).expect D)+Real.log a := by
    simp only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one]
    rw [(P y).factor_expect θ D a hfac,Real.log_mul (ne_of_gt ha) (ne_of_gt (hDP y)),add_comm]
  have hθ₀ : θ s₀=Real.log (1+D s₀)+Real.log a := by
    rw [← Real.log_exp (θ s₀),hfac s₀,Real.log_mul (ne_of_gt ha) (ne_of_gt hd),add_comm]
  have he : KernelTower.backwardLog n T (fun j => m j.succ)
      (fun y => (P y).logMean 1 θ)-θ s₀=
      KernelTower.backwardLog n T (fun j => m j.succ)
        (fun y => Real.log (1+(P y).expect D))-Real.log (1+D s₀) := by
    simp_rw [hlog]
    rw [KernelTower.backwardLog_add n T _ hnz,hθ₀]
    ring
  rw [he]
  apply Tendsto.sub
  · apply KernelTower.tendsto_backwardLog
    intro y
    simpa only [one_mul,id_eq] using
      (((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 (1:ℝ)) (𝓝 1)).mul_const ((P y).expect D)).const_add 1).log (by simpa only [one_mul] using ne_of_gt (hDP y))
  · simpa only [one_mul,id_eq] using
      (((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 (1:ℝ)) (𝓝 1)).mul_const (D s₀)).const_add 1).log (by simpa only [one_mul] using ne_of_gt hd)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixedEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology

lemma mixedSpinLaw_factor {p : ℕ} (z : InteractionSample p)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    (mixedSpinLaw sel s x).expect (fun σ => z.2.2.1*∏ l,z.2.2.2 l (σ l))=
      mixedFactor z sel s x := by
  classical
  unfold mixedSpinLaw mixedFactor
  rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_pi_product]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  cases h : sel l <;> simp only [Bool.false_eq_true,↓reduceIte,FiniteLaw.expect_point]
  rfl

lemma mixedEnergy_bound {p : ℕ} (z : InteractionSample p)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    |mixedEnergy z sel s x|≤‖z.1‖ := by
  have h := (mixedSpinLaw sel s x).logMean_stability (m := 1) zero_lt_one
    (f := z.1) (g := fun _ => 0) (c := ‖z.1‖)
    (fun σ => by simpa only [sub_zero,Real.norm_eq_abs] using norm_le_pi_norm z.1 σ)
  simpa only [mixedEnergy,FiniteLaw.logMean_const _ one_ne_zero,sub_zero] using h

lemma measurable_mixedEnergy {p : ℕ} (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    Measurable (fun z : InteractionSample p => mixedEnergy z sel s x) :=
  FiniteLaw.measurable_logMean _ _ (fun σ => by fun_prop)

namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

lemma measurable_mixedEnergyAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (sel : Fin p → Bool) :
    Measurable (fun z => mixedEnergyAvg T Q U V x m z sel) := by
  apply FiniteLaw.measurable_expect
  intro i
  apply FiniteLaw.measurable_expect
  intro r
  apply KernelTower.measurable_backwardLog
  intro y
  exact measurable_mixedEnergy sel _ _

lemma mixedEnergyAvg_bound (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ)
    (z : InteractionSample p) (sel : Fin p → Bool) :
    |mixedEnergyAvg T Q U V x m z sel|≤‖z.1‖ := by
  apply FiniteLaw.abs_expect_le
  intro i
  apply FiniteLaw.abs_expect_le
  intro r
  exact KernelTower.backwardLog_bound n _ _ hm (fun y => mixedEnergy_bound z sel _ _)

lemma integrable_mixedEnergyAvg (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ) (sel : Fin p → Bool) :
    Integrable (fun z => mixedEnergyAvg T Q U V x m z sel) M.disorder.toMeasure := by
  apply hM.interaction_integrable.mono' (measurable_mixedEnergyAvg T Q U V x m sel).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using mixedEnergyAvg_bound T Q U V x m hm z sel)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

lemma abs_integral_le_bound_ae {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} {B : ℝ}
    (h : ∀ᵐ x ∂μ, |f x|≤B) : |∫ x,f x ∂μ|≤B := by
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
      (h.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx))

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

lemma mixedNormalizedAvg_bound (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ)
    (z : InteractionSample p)
    (hz : 0<z.2.1 ∧ ∀ s : Fin p → Spin,
      Real.exp (z.1 s)=z.2.1*(1+z.2.2.1*∏ l,z.2.2.2 l (s l)) ∧
      |z.2.2.1*∏ l,z.2.2.2 l (s l)|<1)
    (sel : Fin p → Bool) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    |mixedNormalizedAvg T Q U V x m z sel t|≤2*‖z.1‖ := by
  unfold mixedNormalizedAvg mixedLogAvg
  rw [← FiniteLaw.expect_const (P := FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N))))
    (Real.log (1+t*referenceD z)),← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le
  intro i
  rw [← FiniteLaw.expect_const (P := FiniteLaw.pi (fun _ : Fin p => Q)) (Real.log (1+t*referenceD z)),
    ← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le
  intro r
  let P := fun w : FinitePath (Ω×(Fin p → Λ)) n => mixedSpinLaw sel
    (fun l => V (KernelTower.pathFst n w) (i l))
    (fun l => x (r l) (KernelTower.pathMap (fun a : Fin p → Λ => a l) n (KernelTower.pathSnd n w)))
  have hh := normalized_logInsertion_bound
    (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j)))) m hm P
    z.1 (fun s => z.2.2.1*∏ l,z.2.2.2 l (s l)) z.2.1 hz.1 (fun s => (hz.2 s).1)
    (fun _ => false) (fun s => (hz.2 s).2) (norm_nonneg z.1)
    (fun s => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 s) ht0 ht
  simp only [P,mixedSpinLaw_factor] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma mixedNormalizedAvg_limit (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hnz : ∀ j : Fin n,m j.succ≠0)
    (z : InteractionSample p)
    (hz : 0<z.2.1 ∧ ∀ s : Fin p → Spin,
      Real.exp (z.1 s)=z.2.1*(1+z.2.2.1*∏ l,z.2.2.2 l (s l)) ∧
      |z.2.2.1*∏ l,z.2.2.2 l (s l)|<1)
    (sel : Fin p → Bool) :
    Tendsto (mixedNormalizedAvg T Q U V x m z sel) (𝓝 1)
      (𝓝 (mixedEnergyAvg T Q U V x m z sel-z.1 (fun _ => false))) := by
  let I : FiniteLaw (Fin p → Fin N) := FiniteLaw.pi (fun _ => FiniteLaw.uniform)
  let P (i : Fin p → Fin N) (r : Fin p → R) (w : FinitePath (Ω×(Fin p → Λ)) n) := mixedSpinLaw sel
    (fun l => V (KernelTower.pathFst n w) (i l))
    (fun l => x (r l) (KernelTower.pathMap (fun a : Fin p → Λ => a l) n (KernelTower.pathSnd n w)))
  have hh (i : Fin p → Fin N) (r : Fin p → R) := normalized_logInsertion_limit
    (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j)))) m hnz (P i r)
    z.1 (fun s => z.2.2.1*∏ l,z.2.2.2 l (s l)) z.2.1 hz.1 (fun s => (hz.2 s).1)
    (fun _ => false) (fun s => (hz.2 s).2)
  have hl := I.tendsto_expect _ _ (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).tendsto_expect _ _ (hh i))
  simp only [P,I,mixedSpinLaw_factor,FiniteLaw.expect_sub,FiniteLaw.expect_const] at hl
  convert hl using 1 <;> rfl

lemma measurable_mixedNormalizedAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (sel : Fin p → Bool) (t : ℝ) :
    Measurable (fun z => mixedNormalizedAvg T Q U V x m z sel t) := by
  apply (measurable_mixedLogAvg T Q U V x m sel t).sub
  unfold referenceD
  fun_prop

lemma integrable_mixedNormalizedAvg (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ)
    (sel : Fin p → Bool) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    Integrable (fun z => mixedNormalizedAvg T Q U V x m z sel t) M.disorder.toMeasure := by
  apply (hM.interaction_integrable.const_mul 2).mono'
    (measurable_mixedNormalizedAvg T Q U V x m sel t).aestronglyMeasurable
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using mixedNormalizedAvg_bound T Q U V x m hm z hz sel ht0 ht

lemma regularization_nonneg (k : ℕ) : 0 ≤ regularization k := by
  unfold regularization
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have hh : 1/((k:ℝ)+1)≤1 := (div_le_one (by positivity : (0:ℝ)<k+1)).mpr (by linarith)
  linarith
lemma regularization_lt_one (k : ℕ) : regularization k<1 := by
  unfold regularization
  have hh : (0:ℝ)<1/((k:ℝ)+1) := by positivity
  linarith
lemma regularization_limit : Tendsto regularization atTop (𝓝 1) := by
  unfold regularization
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

lemma integral_mixedNormalizedAvg_limit (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ) (sel : Fin p → Bool) :
    Tendsto (fun k => ∫ z,mixedNormalizedAvg T Q U V x m z sel (regularization k) ∂M.disorder.toMeasure)
      atTop (𝓝 ((∫ z,mixedEnergyAvg T Q U V x m z sel ∂M.disorder.toMeasure)-
        ∫ z,z.1 (fun _ => false) ∂M.disorder.toMeasure)) := by
  have href : Integrable (fun z : InteractionSample p => z.1 (fun _ => false)) M.disorder.toMeasure :=
    hM.interaction_integrable.mono' (by fun_prop) (ae_of_all _ (fun z => norm_le_pi_norm z.1 _))
  rw [← integral_sub (integrable_mixedEnergyAvg M hM T Q U V x m hm sel) href]
  apply tendsto_integral_of_dominated_convergence (fun z : InteractionSample p => 2*‖z.1‖)
  · intro k
    exact (measurable_mixedNormalizedAvg T Q U V x m sel _).aestronglyMeasurable
  · exact hM.interaction_integrable.const_mul 2
  · intro k
    filter_upwards [hM.factorization] with z hz
    simpa only [Real.norm_eq_abs] using mixedNormalizedAvg_bound T Q U V x m hm z hz sel
      (regularization_nonneg k) (regularization_lt_one k)
  · filter_upwards [hM.factorization] with z hz
    exact (mixedNormalizedAvg_limit T Q U V x m (fun j => ne_of_gt (hm j)) z hz sel).comp regularization_limit


/-- First-moment common-tree insertion inequality (unregularized). -/
lemma integral_mixedEnergy_combination_nonpos (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hstrict : ∀ j : Fin n,0 < m j.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) :
    (∫ z,mixedEnergyAvg T Q U V x m z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedEnergyAvg T Q U V x m z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedEnergyAvg T Q U V x m z (fun _ => false) ∂M.disorder.toMeasure) ≤0 := by
  have hp : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by
    rw [Nat.cast_sub (by have h := hM.arity; omega : 1≤p)]; norm_num
  have hr (k : ℕ) :
      (∫ z,mixedNormalizedAvg T Q U V x m z (fun _ => true) (regularization k) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedNormalizedAvg T Q U V x m z (fun l => decide (l=j)) (regularization k) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedNormalizedAvg T Q U V x m z (fun _ => false) (regularization k) ∂M.disorder.toMeasure) ≤0 := by
    have ht0 := regularization_nonneg k
    have ht := regularization_lt_one k
    have ht' : |regularization k|<1 := by rwa [abs_of_nonneg ht0]
    have hi (sel : Fin p → Bool) := integrable_mixedLogAvg M hM T Q U V x m hm hpos (fun l => ne_of_gt (hstrict l)) hroot hend sel ht'
    have hn (sel : Fin p → Bool) := integrable_mixedNormalizedAvg M hM T Q U V x m hstrict sel ht0 ht
    have hd : Integrable (fun z => Real.log (1+regularization k*referenceD z)) M.disorder.toMeasure := by
      convert (hi (fun _ => false)).sub (hn (fun _ => false)) using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      simp only [Pi.sub_apply,mixedNormalizedAvg]
      ring
    simp only [mixedNormalizedAvg]
    rw [integral_sub (hi _) hd,integral_sub (hi _) hd,integral_sub (hi _) hd]
    have hs := integral_mixedLog_combination_nonpos M hM T Q U V x m hm hpos
      (fun l => ne_of_gt (hstrict l)) hroot hend j ht0 ht
    rw [hp] at hs ⊢
    nlinarith only [hs]
  have hlim := ((integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun _ => true)).sub
    ((integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun l => decide (l=j))).const_mul (p:ℝ))).add
    ((integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun _ => false)).const_mul ((p-1:ℕ):ℝ))
  have hs := le_of_tendsto hlim (Eventually.of_forall hr)
  rw [hp] at hs ⊢
  nlinarith only [hs]

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass
open scoped BigOperators

lemma mixedSpinLaw_single {p : ℕ} (j : Fin p) (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedSpinLaw (fun a => decide (a=j)) s x=
      mixedSpinLaw (fun a => decide (a=j)) (fun _ => s j) x := by
  unfold mixedSpinLaw
  congr 1
  funext a
  by_cases h : a=j
  · subst a; rfl
  · simp [h]

lemma mixedEnergy_single {p : ℕ} (z : InteractionSample p) (j : Fin p)
    (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedEnergy z (fun a => decide (a=j)) s x=
      mixedEnergy z (fun a => decide (a=j)) (fun _ => s j) x := by
  unfold mixedEnergy
  rw [mixedSpinLaw_single]

lemma mixedEnergy_last {q : ℕ} (z : InteractionSample (q+1))
    (s : Fin (q+1) → Spin) (x : Fin (q+1) → ℝ) :
    mixedEnergy z (fun a => decide (a=Fin.last q)) s x=
      message z.1 (fun i => x i.castSucc) (s (Fin.last q)) := by
  classical
  unfold mixedEnergy mixedSpinLaw FiniteLaw.logMean FiniteLaw.expMoment
  simp only [one_mul,div_one]
  apply congrArg Real.log
  unfold FiniteLaw.expect FiniteLaw.pi
  rw [← (Fin.snocEquiv (fun _ : Fin (q+1) => Spin)).sum_comp]
  simp only [Fintype.sum_prod_type,Fin.snocEquiv_apply,Fin.prod_univ_castSucc,
    Fin.snoc_castSucc,Fin.snoc_last,Fin.castSucc_ne_last,decide_false,Bool.false_eq_true,
    ↓reduceIte,decide_true,FiniteLaw.point]
  simp only [Finset.sum_ite_irrel,mul_ite,ite_mul,zero_mul,mul_zero,mul_one,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  have he : (Fin.snocEquiv (fun _ : Fin (q+1) => Spin)) (s (Fin.last q),a)=
      appendSpin (p := q+1) a (s (Fin.last q)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snocEquiv_apply,Fin.snoc_last] using (appendSpin_last a (s (Fin.last q))).symm
    · simpa only [Fin.snocEquiv_apply,Fin.snoc_castSucc] using (appendSpin_castSucc a (s (Fin.last q)) j).symm
  simp only [he,qLaw,mul_comm]
  rfl

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionPoissonAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

lemma poisson_average_integrable (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : Integrable f (poissonMeasure ρ) := by
  apply ((integrable_const B).add ((poisson_integrable_count ρ).const_mul D)).mono'
    (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_apply] using h k)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TowerArraySplit
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma splitFirst_projects (n l : ℕ) (T : KernelTower Ω n) (U : Fin (l+1) → KernelTower Λ n) :
    Projects (splitFirst l) n (prod n T (pi n U))
      (prod n (prod n T (pi n (fun i => U i.succ))) (U 0)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (fun i => (U i).2 (a.2 i))⟩
    intro f
    change (T.1.bind (fun _ => FiniteLaw.pi (fun i => (U i).1))).expect (fun z => f (splitFirst l z)) =
      ((T.1.bind (fun _ => FiniteLaw.pi (fun i : Fin l => (U i.succ).1))).bind (fun _ => (U 0).1)).expect f
    simp only [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    rw [FiniteLaw.expect_pi_cons]
    rw [FiniteLaw.expect_comm]
    apply FiniteLaw.expect_congr
    intro b
    apply FiniteLaw.expect_congr
    intro c
    simp only [splitFirst,Fin.cons_zero,Fin.cons_succ]

lemma prod_empty_projects (n : ℕ) (T : KernelTower Ω n) (U : Fin 0 → KernelTower Λ n) :
    Projects Prod.fst n (prod n T (pi n U)) T := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (fun i => (U i).2 (a.2 i))⟩
    intro f
    change (T.1.bind (fun _ => FiniteLaw.pi (fun i => (U i).1))).expect (fun a => f a.1)=T.1.expect f
    simp only [FiniteLaw.expect_bind,FiniteLaw.expect_const]

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TowerTerminalPad
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
lemma logMean_bind_point (P : FiniteLaw Ω) (a : Λ) (m : ℝ) (f : Ω×Λ → ℝ) :
    (P.bind (fun _ => point a)).logMean m f=P.logMean m (fun s => f (s,a)) := by
  simp only [logMean,expMoment,expect_bind,expect_point]
lemma logMean_point_bind (a : Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω×Λ → ℝ) :
    ((point a).bind (fun _ => Q)).logMean m f=Q.logMean m (fun s => f (a,s)) := by
  simp only [logMean,expMoment,expect_bind,expect_point]
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma backwardLog_terminal_pad (a : Ω) (b : Λ) (P : FiniteLaw Ω)
    (r : ℕ) (U : KernelTower Λ r) (m : Fin (r+1) → ℝ) (F : Ω → FinitePath Λ r → ℝ) :
    backwardLog (r+1) (prod (r+1) (terminalTower a P r) (pad b r U)) m
      (fun y => F (terminalState r (pathFst (r+1) y)) (pathPrefix r (pathSnd (r+1) y))) =
      backwardLog r U (fun d => m d.castSucc)
        (fun y => P.logMean (m (Fin.last r)) (fun s => F s y)) := by
  induction r with
  | zero =>
    change (P.bind (fun _ => FiniteLaw.point b)).logMean (m 0) (fun z => F z.1 ()) =
      P.logMean (m (Fin.last 0)) (fun s => F s ())
    exact FiniteLaw.logMean_bind_point P b _ _
  | succ r ih =>
    simp only [backwardLog,prod,terminalTower,pad,pathFst,pathSnd,terminalState,pathPrefix]
    rw [FiniteLaw.logMean_point_bind]
    apply congrArg (U.1.logMean (m 0))
    funext z
    exact ih (U.2 z) (fun d => m d.succ) (fun s y => F s (z,y))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperRootInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

lemma mixedRootIncrement_eq (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (f : FinitePath Ω n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) :
    mixedRootIncrement T Q U V x m f z sel =
      mixedEnergyAvg (KernelTower.tilt n T (fun j => m j.succ) f) Q U V x m z sel := by
  unfold mixedRootIncrement mixedEnergyAvg
  apply FiniteLaw.expect_congr
  intro i
  apply FiniteLaw.expect_congr
  intro r
  rw [← KernelTower.backwardLog_prod_fst n T (KernelTower.piTower n (fun j : Fin p => U (r j)))
    (fun j => m j.succ) f,KernelTower.insertion,KernelTower.tilt_prod_fst]

/-- The local upper interpolation decrement, now a difference of actual
unperturbed root free energies rather than an assumed tilted increment. -/
lemma integral_mixedRoot_combination_nonpos (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j,0 ≤ m j)
    (hstrict : ∀ j : Fin n,0 < m j.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) :
    (∫ z,mixedRootIncrement T Q U V x m f z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun _ => false) ∂M.disorder.toMeasure) ≤0 := by
  simp only [mixedRootIncrement_eq]
  exact integral_mixedEnergy_combination_nonpos M hM _ Q U V x m hm hpos hstrict hroot hend j

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityProxy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
namespace FiniteLaw
lemma pi_point {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i,Fintype (α i)] (a : (i : ι) → α i) :
    pi (fun i => point (a i))=point a := by
  classical
  apply ext
  intro b
  by_cases h : a=b
  · subst b; simp [pi,point]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [pi,point,ite_eq_right (Ne.symm h)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right (Ne.symm hi))
end FiniteLaw

lemma mixedEnergy_true {p : ℕ} (z : InteractionSample p)
    (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedEnergy z (fun _ => true) s x=z.1 s := by
  unfold mixedEnergy mixedSpinLaw
  simp only [↓reduceIte,FiniteLaw.pi_point,FiniteLaw.logMean,FiniteLaw.expMoment,
    FiniteLaw.expect_point,one_mul,div_one,Real.log_exp]

lemma mixedEnergy_false {p : ℕ} (z : InteractionSample p)
    (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedEnergy z (fun _ => false) s x=Real.log (edge z.1 x) := by
  unfold mixedEnergy mixedSpinLaw
  simp only [Bool.false_eq_true,↓reduceIte,FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,
    FiniteLaw.expect,FiniteLaw.pi,qLaw]
  congr 1
  unfold edge
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

lemma mixedRootIncrement_false (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (f : FinitePath Ω n → ℝ) (z : InteractionSample p) :
    mixedRootIncrement T Q U V x m f z (fun _ => false)=edgeRoot Q U x (fun j => m j.succ) z := by
  unfold mixedRootIncrement mixedTreeEnergy edgeRoot
  simp only [mixedEnergy_false]
  have he (r : Fin p → R) := KernelTower.backwardLog_prod_add n T
    (KernelTower.piTower n (fun j : Fin p => U (r j))) (fun j => m j.succ) f
    (fun y => Real.log (edge z.1 (fun j => x (r j)
      (KernelTower.pathMap (fun a : Fin p → Λ => a j) n y))))
  simp only [he,add_sub_cancel_left,FiniteLaw.expect_const]

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperTrial
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.upperTrialMeasurableSpace
local instance upperTrialBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
namespace KernelTower
variable {Ω : Type} [Fintype Ω]
omit [Fintype Ω] in
lemma pathMap_pathPrefix {Λ : Type} (g : Ω → Λ) (n : ℕ) (y : FinitePath Ω (n+1)) :
    pathMap g n (pathPrefix n y)=pathPrefix n (pathMap g (n+1) y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (g y.1,pathMap g n (pathPrefix n y.2))=(g y.1,pathPrefix n (pathMap g (n+1) y.2))
      rw [ih]

lemma piTower_eq_pi {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (T : ι → KernelTower Ω n) : piTower n T=pi n T := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (_,fun (x : ι → Ω) => piTower n (fun i => (T i).2 (x i)))=(_,fun (x : ι → Ω) => pi n (fun i => (T i).2 (x i)))
      congr 1
      funext x
      exact ih _

lemma piTower_pad {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : Ω) (n : ℕ) (T : ι → KernelTower Ω n) :
    piTower (n+1) (fun i => pad a n (T i))=pad (fun _ : ι => a) n (piTower n T) := by
  induction n with
  | zero =>
      change (FiniteLaw.pi (fun _ : ι => FiniteLaw.point a),fun _ => ())=(FiniteLaw.point (fun _ : ι => a),fun _ => ())
      rw [FiniteLaw.pi_point]
  | succ n ih =>
      change (FiniteLaw.pi (fun i => (T i).1),fun (x : ι → Ω) => piTower (n+1) (fun i => pad a n ((T i).2 (x i))))=
        (FiniteLaw.pi (fun i => (T i).1),fun (x : ι → Ω) => pad (fun _ : ι => a) n (piTower n (fun i => (T i).2 (x i))))
      congr 1
      funext x
      exact ih _

omit [Fintype Ω] in
lemma proj_eq_pathMap {ι : Type} (n : ℕ) (y : FinitePath (ι → Ω) n) (i : ι) :
    FinitePath.proj n y i=pathMap (fun a : ι → Ω => a i) n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (y.1 i,FinitePath.proj n y.2 i)=(y.1 i,pathMap (fun a : ι → Ω => a i) n y.2)
      rw [ih]
end KernelTower

namespace PrescribedTree
variable {Λ R : Type} [Fintype Λ] [Fintype R]

attribute [local instance] OAI.DilutedSpinGlass.upperTrialMeasurableSpace
lemma finite_trialLog {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (F : (ι → ℝ) → ℝ) :
    trialLog r (finiteTrialLaw r Q U x) m F =
      (FiniteLaw.pi (fun _ : ι => Q)).expect (fun a =>
        KernelTower.backwardLog r (KernelTower.piTower r (fun i => U (a i))) m
          (fun y => F (fun i => x (a i) (KernelTower.pathMap (fun b : ι → Λ => b i) r y)))) := by
  unfold trialLog finiteTrialLaw
  rw [FiniteLaw.integral_pi_asProbability]
  apply FiniteLaw.expect_congr
  intro a
  rw [KernelTower.piTower_eq_pi]
  exact (KernelTower.backwardLog_realEncode r (fun i => U (a i)) (fun i => x (a i)) F m).symm.trans
    (by congr 1; funext y; simp only [KernelTower.proj_eq_pathMap])

lemma edgeRoot_pad (r : ℕ) (a : Λ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)≠0)
    {p : ℕ} (z : InteractionSample p) :
    edgeRoot (Λ := Λ) (R := R) (n := r+1) (p := p) Q (fun b : R => KernelTower.pad a r (U b))
      (fun (b : R) (y : FinitePath Λ (r+1)) => x b (KernelTower.pathPrefix r y)) m z =
      trialLog (ι := Fin p) r (finiteTrialLaw r Q U x) (fun j => m j.castSucc) (fun y => Real.log (edge z.1 y)) := by
  refine Eq.trans ?_ (finite_trialLog r Q U x (fun j => m j.castSucc) (fun y => Real.log (edge z.1 y))).symm
  change (FiniteLaw.pi (fun _ : Fin p => Q)).expect _ =
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect _
  apply FiniteLaw.expect_congr
  intro b
  rw [KernelTower.piTower_pad a r (fun i : Fin p => U (b i))]
  have he (y : FinitePath (Fin p → Λ) (r+1)) :
      (fun j => x (b j) (KernelTower.pathPrefix r (KernelTower.pathMap (fun a : Fin p → Λ => a j) (r+1) y)))=
      (fun j => x (b j) (KernelTower.pathMap (fun a : Fin p → Λ => a j) r (KernelTower.pathPrefix r y))) := by
    funext j
    rw [KernelTower.pathMap_pathPrefix]
  simp only [he]
  exact KernelTower.backwardLog_pad (fun _ : Fin p => a) r
    (KernelTower.piTower r (fun i : Fin p => U (b i))) m hend
    (fun y : FinitePath (Fin p → Λ) r => Real.log (edge z.1
      (fun j => x (b j) (KernelTower.pathMap (fun c : Fin p → Λ => c j) r y))))

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalMeanField
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace FiniteLaw
variable {ι κ Ω : Type} [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
lemma expect_pi_curry (Q : ι → κ → FiniteLaw Ω) (f : (ι×κ → Ω) → ℝ) :
    (pi (fun i => pi (Q i))).expect (fun x => f (fun z => x z.1 z.2))=
      (pi (fun z : ι×κ => Q z.1 z.2)).expect f := by
  classical
  symm
  unfold expect
  apply Fintype.sum_equiv (Equiv.curry ι κ Ω)
  intro x
  simp only [pi,Equiv.curry_apply,Function.curry,Fintype.prod_prod_type]

end FiniteLaw
namespace KernelTower
variable {ι κ Ω : Type} [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
lemma pi_curry_projects (n : ℕ) (T : ι → κ → KernelTower Ω n) :
    Projects (fun x : ι → κ → Ω => fun z : ι×κ => x z.1 z.2) n
      (pi n (fun i => pi n (T i))) (pi n (fun z : ι×κ => T z.1 z.2)) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨FiniteLaw.expect_pi_curry (fun i j => (T i j).1),fun a => ih (fun i j => (T i j).2 (a i j))⟩

lemma pi_injective_projects (e : ι → κ) (he : Function.Injective e) (n : ℕ) (T : κ → KernelTower Ω n) :
    Projects (fun x : κ → Ω => fun i => x (e i)) n
      (pi n T) (pi n (fun i => T (e i))) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨FiniteLaw.expect_pi_injective (fun j => (T j).1) e he,fun a => ih (fun j => (T j).2 (a j))⟩

lemma pi_rect_castSucc_projects (n k q : ℕ) (T : Fin k → Fin (q+1) → KernelTower Ω n) :
    Projects (fun x : Fin k → Fin (q+1) → Ω => fun z : Fin k×Fin q => x z.1 z.2.castSucc) n
      (pi n (fun i => piTower n (T i)))
      (piTower n (fun z : Fin k×Fin q => T z.1 z.2.castSucc)) := by
  simp only [piTower_eq_pi]
  exact (pi_curry_projects n T).comp n
    (pi_injective_projects (fun z : Fin k×Fin q => (z.1,z.2.castSucc))
      (by
        intro a b h
        apply Prod.ext
        · exact congrArg (fun z : Fin k×Fin (q+1) => z.1) h
        · exact (Fin.castSucc_injective q) (congrArg (fun z : Fin k×Fin (q+1) => z.2) h)) n _)
end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperCountState
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators

variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] in
lemma pathMap_id (n : ℕ) (y : FinitePath Ω n) : pathMap id n y=y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathMap_cavityProject (l : ℕ) (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathMap (cavityProject (l+1)) n y=pathMap (cavityProject l) n (pathFst n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma cavityEnergy_add (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (l : ℕ) (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f g : FinitePath Ω n → ℝ)
    (y : FinitePath (CavityState Ω Λ p l) n) :
    cavityEnergy V x j l r i z (f+g) y=
      cavityEnergy V x j l r i z f y+g (pathMap (cavityProject l) n y) := by
  induction l with
  | zero =>
    have hy : pathMap id n (show FinitePath Ω n from y)=y := pathMap_id n y
    exact congrArg (fun t => f y+g t) hy.symm
  | succ l ih =>
    change cavityEnergy V x j l r.2 i.2 z.2 (f+g) (pathFst n y)+_=_
    rw [ih,pathMap_cavityProject]
    dsimp only [cavityEnergy]
    ring

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma cavityEnergy_bound (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (l : ℕ) (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |cavityEnergy V x j l r i z f y|≤B+∑ a,‖(rootArray l z a).1‖ := by
  induction l with
  | zero => simpa [cavityEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    calc
      _ ≤ (B+∑ a,‖(rootArray l z.2 a).1‖)+‖z.1.1‖ :=
        add_le_add (ih r.2 i.2 z.2 (pathFst n y)) (mixedEnergy_bound z.1 (fun a => decide (a=j)) _ _)
      _ = _ := by simp only [rootArray,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]; ring

omit [Fintype R] [NeZero N] in
lemma cavityRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |cavityRoot T U V x m j l r i z f|≤B+∑ a,‖(rootArray l z a).1‖ :=
  backwardLog_bound n _ m hm (cavityEnergy_bound V x j l r i z f hf)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {ι Ω Λ R : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype R] in
lemma cavityJoin_projects (T : ι → KernelTower Ω n) (U : R → KernelTower Λ n)
    (l : ℕ) (r : RootPath (Fin p → R) l) (c : RootPath ι l) :
    KernelTower.Projects (cavityJoin l c) n
      (KernelTower.pi n (fun i => cavityTower (T i) U l r))
      (cavityTower (KernelTower.pi n T) U l r) := by
  induction l with
  | zero => exact KernelTower.Projects.refl n _
  | succ l ih =>
    have h := KernelTower.pi_prod_projects n (fun i => cavityTower (T i) U l r.2)
      (fun _ : ι => piTower n (fun j => U (r.1 j))) c.1
    have g := KernelTower.Projects.prod n (ih r.2 c.2)
      (KernelTower.Projects.refl n (piTower n (fun j => U (r.1 j))))
    exact KernelTower.Projects.comp n h g

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma pathFst_cavityJoin (l : ℕ) (c : RootPath ι (l+1))
    (y : FinitePath (ι → CavityState Ω Λ p (l+1)) n) :
    pathFst n (pathMap (cavityJoin (Ω := Ω) (Λ := Λ) (p := p) (l+1) c) n y)=
      pathMap (cavityJoin l c.2) n (pathMap (fun a i => (a i).1) n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma pathSnd_cavityJoin (l : ℕ) (c : RootPath ι (l+1))
    (y : FinitePath (ι → CavityState Ω Λ p (l+1)) n) :
    pathSnd n (pathMap (cavityJoin (Ω := Ω) (Λ := Λ) (p := p) (l+1) c) n y)=
      pathSnd n (FinitePath.proj n y c.1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma cavityProject_join (l : ℕ) (c : RootPath ι l)
    (a : ι → CavityState Ω Λ p l) (i : ι) :
    cavityProject l (cavityJoin l c a) i=cavityProject l (a i) := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih c.2 (fun i => (a i).1)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperDatum
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

lemma rootArray_rootMap {X Y : Type} (f : X → Y) (k : ℕ) (z : RootPath X k) (i : Fin k) :
    rootArray k (rootMap f k z) i=f (rootArray k z i) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases rfl (fun i => ?_) i
    exact ih z.2 i

lemma measurable_rootMap {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (k : ℕ) : Measurable (rootMap f k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact (hf.comp measurable_fst).prodMk (ih.comp measurable_snd)

namespace PrescribedTree
variable {Ω Λ R X : Type} [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace X]
    {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma measurable_cavityEnergy (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : X → FinitePath Ω n → ℝ) (hf : ∀ y,Measurable (fun a => f a y))
    (y : FinitePath (CavityState Ω Λ p l) n) :
    Measurable (fun a => cavityEnergy V x j l r i (z a) (f a) y) := by
  induction l with
  | zero => exact hf y
  | succ l ih =>
    apply (ih r.2 i.2 (fun a => (z a).2) (measurable_snd.comp hz) (KernelTower.pathFst n y)).add
    exact (measurable_mixedEnergy _ _ _).comp (measurable_fst.comp hz)

omit [Fintype R] [NeZero N] in
lemma measurable_cavityRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : X → FinitePath Ω n → ℝ) (hf : ∀ y,Measurable (fun a => f a y)) :
    Measurable (fun a => cavityRoot T U V x m j l r i (z a) (f a)) :=
  KernelTower.measurable_backwardLog n _ m (measurable_cavityEnergy V x j l r i z hz f hf)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootMapLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
lemma measurePreserving_rootMap {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (k : ℕ) :
    MeasurePreserving (rootMap f k) (rootLaw k (fun _ => μ)) (rootLaw k (fun _ => ν)) := by
  induction k with
  | zero => exact MeasurePreserving.id _
  | succ k ih => exact hf.prod ih

lemma integral_rootMap {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (k : ℕ) (F : RootPath Y k → ℝ)
    (hF : Measurable F) :
    (∫ z,F (rootMap f k z) ∂rootLaw k (fun _ => μ))=∫ w,F w ∂rootLaw k (fun _ => ν) :=
by
  rw [← (measurePreserving_rootMap hf k).map_eq,
    integral_map (measurable_rootMap f hf.measurable k).aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySeparable
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [NeZero N] in
lemma path_proj_fst (l : ℕ)
    (y : FinitePath (Fin N → CavityState Ω Λ p (l+1)) n) (i : Fin N) :
    FinitePath.proj n (pathMap (fun a s => (a s).1) n y) i=
      pathFst n (FinitePath.proj n y i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [NeZero N] in
lemma path_proj_join (l : ℕ) (c : RootPath (Fin N) l)
    (y : FinitePath (Fin N → CavityState Ω Λ p l) n) (i : Fin N) :
    FinitePath.proj n (pathMap (cavityProject l) n (pathMap (cavityJoin l c) n y)) i=
      pathMap (cavityProject l) n (FinitePath.proj n y i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_join l c y.1 i) (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma cavityEnergy_join (V : Fin N → FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (l : ℕ) (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : Fin N → FinitePath Ω n → ℝ)
    (y : FinitePath (Fin N → CavityState Ω Λ p l) n) :
    cavityEnergy (fun y s => V s (FinitePath.proj n y s)) x j l r i z
      (fun y => ∑ s,f s (FinitePath.proj n y s))
      (pathMap (cavityJoin l (rootMap (fun a => a j) l i)) n y)=
      ∑ s,allocatedEnergy (V s) x j s l r (rootMap (fun a => a j) l i) z (f s)
        (FinitePath.proj n y s) := by
  induction l with
  | zero =>
    change (∑ s,f s (FinitePath.proj n (pathMap id n y) s))=∑ s,f s (FinitePath.proj n y s)
    rw [pathMap_id]
  | succ l ih =>
    simp only [cavityEnergy,allocatedEnergy,rootMap,pathFst_cavityJoin]
    rw [ih]
    simp only [path_proj_fst,Finset.sum_add_distrib]
    congr 1
    unfold mixedTreeEnergy
    rw [mixedEnergy_single]
    simp only [pathFst_cavityJoin,pathSnd_cavityJoin,path_proj_join,path_proj_fst]
    simp only [singleBlockEnergy]
    rw [Finset.sum_eq_single (i.1 j)]
    · simp only [ite_true]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

omit [Fintype R] [NeZero N] in
lemma cavityRoot_separable (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : Fin N → FinitePath Ω n → ℝ) :
    cavityRoot (KernelTower.pi n T) U (fun y s => V s (FinitePath.proj n y s)) x m j l r i z
      (fun y => ∑ s,f s (FinitePath.proj n y s))=
      ∑ s,backwardLog n (cavityTower (T s) U l r) m
        (allocatedEnergy (V s) x j s l r (rootMap (fun a => a j) l i) z (f s)) := by
  unfold cavityRoot
  rw [← backwardLog_of_projects n (cavityJoin_projects T U l r (rootMap (fun a => a j) l i))]
  simp_rw [cavityEnergy_join]
  exact backwardLog_pi_sum _ _ _ _

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_EnergyInsertionMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory

lemma measurePreserving_selectRoot {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (l : ℕ) (b : RootPath Bool l) :
    MeasurePreserving (selectRoot (X := X) l b) (rootLaw l (fun _ => μ))
      (rootLaw (selectedCount l b) (fun _ => μ)) := by
  induction l with
  | zero => exact MeasurePreserving.id _
  | succ l ih =>
    cases b with | mk a b =>
      cases a
      · change MeasurePreserving (fun z : X×RootPath X l => selectRoot l b z.2)
          (μ.prod (rootLaw l (fun _ => μ))) (rootLaw (selectedCount l b) (fun _ => μ))
        exact (ih b).comp (measurePreserving_snd (μ := μ) (ν := rootLaw l (fun _ => μ)))
      · change MeasurePreserving (fun z : X×RootPath X l => (z.1,selectRoot l b z.2))
          (μ.prod (rootLaw l (fun _ => μ))) (μ.prod (rootLaw (selectedCount l b) (fun _ => μ)))
        exact (MeasurePreserving.id μ).prod (ih b)

lemma integral_selectRoot {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (l : ℕ) (b : RootPath Bool l)
    (F : RootPath X (selectedCount l b) → ℝ) (hF : Measurable F) :
    (∫ z,F (selectRoot l b z) ∂rootLaw l (fun _ => μ))=
      ∫ z,F z ∂rootLaw (selectedCount l b) (fun _ => μ) := by
  have h := measurePreserving_selectRoot μ l b
  rw [← h.map_eq,integral_map h.measurable.aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRootIncrement
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
lemma Projects.prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n) :
    Projects Prod.fst n (KernelTower.prod n T U) T := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (U.2 a.2)⟩
    intro f
    change (T.1.bind (fun _ => U.1)).expect (fun z => f z.1)=T.1.expect f
    simp only [FiniteLaw.expect_bind,FiniteLaw.expect_const]

omit [Fintype Ω] [Fintype Λ] in
lemma pathMap_fst (n : ℕ) (y : FinitePath (Ω×Λ) n) :
    pathMap Prod.fst n y=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype R] in
lemma selectCavity_projects (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (l : ℕ) (b : RootPath Bool l) (r : RootPath (Fin p → R) l) :
    Projects (selectCavity (Ω := Ω) (Λ := Λ) (p := p) l b) n
      (cavityTower T U l r) (cavityTower T U (selectedCount l b) (selectRoot l b r)) := by
  induction l with
  | zero => exact Projects.refl n T
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · change Projects (fun z : CavityState Ω Λ p l × (Fin p → Λ) => selectCavity l b z.1) n
        (KernelTower.prod n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j))))
        (cavityTower T U (selectedCount l b) (selectRoot l b r.2))
      exact Projects.comp n (Projects.prod_fst n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j)))) (ih b r.2)
    · change Projects (fun z : CavityState Ω Λ p l × (Fin p → Λ) => (selectCavity l b z.1,id z.2)) n
        (KernelTower.prod n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j))))
        (KernelTower.prod n (cavityTower T U (selectedCount l b) (selectRoot l b r.2)) (piTower n (fun j => U (r.1 j))))
      exact Projects.prod n (ih b r.2) (Projects.refl n (piTower n (fun j => U (r.1 j))))

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_select (l : ℕ) (b : RootPath Bool l) (a : CavityState Ω Λ p l) :
    cavityProject (selectedCount l b) (selectCavity l b a)=cavityProject l a := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v <;> simpa only [selectCavity,selectedCount,Bool.false_eq_true,↓reduceDIte,↓reduceIte,cavityProject] using ih b a.1

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_pathSelect (l : ℕ) (b : RootPath Bool l) (y : FinitePath (CavityState Ω Λ p l) n) :
    pathMap (cavityProject (selectedCount l b)) n (pathMap (selectCavity l b) n y)=
      pathMap (cavityProject l) n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_select l b y.1) (ih y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityMaskEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_select_true (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathFst n (pathMap (selectCavity (l+1) (true,b)) n y)=
      pathMap (selectCavity l b) n (pathFst n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathSnd_select_true (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathSnd n (pathMap (selectCavity (l+1) (true,b)) n y)=pathSnd n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma path_select_false (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathMap (selectCavity (l+1) (false,b)) n y=
      pathMap (selectCavity l b) n (pathFst n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_select (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ)
    (b : RootPath Bool l) (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    activeEnergy V x j (selectedCount l b) (selectRoot l b r) (selectRoot l b z) f
      (pathMap (selectCavity l b) n y)=maskedEnergy V x j l b r z f y := by
  induction l with
  | zero => exact congrArg f (pathMap_id n (show FinitePath Ω n from y))
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · change activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f
        (pathMap (selectCavity (l+1) (false,b)) n y)=maskedEnergy V x j l b r.2 z.2 f (pathFst n y)+0
      exact (congrArg (activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f)
        (path_select_false l b y)).trans ((ih b r.2 z.2 (pathFst n y)).trans (add_zero _).symm)
    · change activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f
          (pathFst n (pathMap (selectCavity (l+1) (true,b)) n y))+
        singleBlockEnergy V x j (selectedCount l b) r.1 z.1 (pathMap (selectCavity (l+1) (true,b)) n y)=
        maskedEnergy V x j l b r.2 z.2 f (pathFst n y)+singleBlockEnergy V x j l r.1 z.1 y
      apply congrArg₂ (fun a b : ℝ => a+b)
      · exact (congrArg (activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f)
          (pathFst_select_true l b y)).trans (ih b r.2 z.2 (pathFst n y))
      · unfold singleBlockEnergy
        have hfst := pathFst_select_true l b y
        have hsnd := pathSnd_select_true l b y
        have hpjs := cavityProject_pathSelect l b (pathFst n y)
        apply congrArg₂ (mixedEnergy z.1 (fun a => decide (a=j)))
        · funext a
          exact congrArg V ((congrArg (pathMap (cavityProject (selectedCount l b)) n) hfst).trans hpjs)
        · funext a
          exact congrArg (fun w => x (r.1 a) (pathMap (fun b : Fin p → Λ => b a) n w)) hsnd

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma allocatedEnergy_mask (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    allocatedEnergy V x j s l r c z f y=
      maskedEnergy V x j l (rootMap (fun a => decide (a=s)) l c) r z f y := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [allocatedEnergy,maskedEnergy,rootMap,decide_eq_true_eq,ih]

omit [Fintype R] [NeZero N] in
lemma allocatedRoot_selected (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (m : Fin n → ℝ) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) :
    backwardLog n (cavityTower T U l r) m (allocatedEnergy V x j s l r c z f)=
      backwardLog n (cavityTower T U (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        (selectRoot l (rootMap (fun a => decide (a=s)) l c) r)) m
        (activeEnergy V x j (selectedCount l (rootMap (fun a => decide (a=s)) l c))
          (selectRoot l (rootMap (fun a => decide (a=s)) l c) r)
          (selectRoot l (rootMap (fun a => decide (a=s)) l c) z) f) := by
  rw [← backwardLog_of_projects n (selectCavity_projects T U l (rootMap (fun a => decide (a=s)) l c) r)]
  congr 1
  funext y
  rw [activeEnergy_select,allocatedEnergy_mask]

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype R] in
lemma cavityPack_projects (T : KernelTower Ω n) (U : R → KernelTower Λ n) (l : ℕ)
    (r : RootPath (Fin p → R) l) :
    Projects (cavityPack l) n
      (prod n T (pi n (fun i : Fin l => piTower n (fun j => U (rootArray l r i j)))))
      (cavityTower T U l r) := by
  induction l with
  | zero => exact prod_empty_projects n T _
  | succ l ih =>
    have hg := splitFirst_projects n l T (fun i => piTower n (fun j => U (rootArray (l+1) r i j)))
    have hh := (ih r.2).prod n (Projects.refl n (piTower n (fun j => U (r.1 j))))
    exact hg.comp n hh

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_pack (l : ℕ) (z : Ω × (Fin l → Fin p → Λ)) :
    cavityProject l (cavityPack l z)=z.1 := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih (z.1,fun i => z.2 i.succ)

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_pack (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathFst n (pathMap (cavityPack (l+1)) n y)=
      pathMap (cavityPack l) n (pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => (z.1,fun i => z.2 i.succ)) n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathSnd_pack (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathSnd n (pathMap (cavityPack (l+1)) n y)=
      pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => z.2 0) n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathProject_pack (l : ℕ) (y : FinitePath (Ω × (Fin l → Fin p → Λ)) n) :
    pathMap (cavityProject l) n (pathMap (cavityPack l) n y)=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_pack l y.1) (ih y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityOldNewMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_tail (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathFst n (pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => (z.1,fun i : Fin l => z.2 i.succ)) n y)=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma singleBlockEnergy_pack (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (j : Fin p) (l : ℕ) (r : Fin p → R) (z : InteractionSample p)
    (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    singleBlockEnergy V x j l r z (pathMap (cavityPack (l+1)) n y)=
      mixedEnergy z (fun a => decide (a=j)) (fun _ => V (pathFst n y))
        (fun a => x (r a) (pathMap (fun b : Ω × (Fin (l+1) → Fin p → Λ) => b.2 0 a) n y)) := by
  unfold singleBlockEnergy
  rw [pathFst_pack,pathProject_pack,pathFst_tail,pathSnd_pack]
  simp only [← pathMap_comp,Function.comp_def]

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_pack (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (Ω × (Fin l → Fin p → Λ)) n) :
    activeEnergy V x j l r z f (pathMap (cavityPack l) n y)=
      f (pathFst n y)+∑ i,mixedEnergy (rootArray l z i) (fun a => decide (a=j))
        (fun _ => V (pathFst n y))
        (fun a => x (rootArray l r i a) (pathMap (fun b : Ω × (Fin l → Fin p → Λ) => b.2 i a) n y)) := by
  induction l with
  | zero =>
    change f (pathMap Prod.fst n y)=f (pathFst n y)+∑ i : Fin 0,_
    simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero,pathMap_fst]
  | succ l ih =>
    change activeEnergy V x j l r.2 z.2 f (pathFst n (pathMap (cavityPack (l+1)) n y))+
      singleBlockEnergy V x j l r.1 z.1 (pathMap (cavityPack (l+1)) n y)=_
    rw [pathFst_pack,ih,singleBlockEnergy_pack,pathFst_tail,Fin.sum_univ_succ]
    simp only [rootArray,Fin.cons_zero,Fin.cons_succ,←pathMap_comp,Function.comp_def]
    ring

omit [Fintype R] in
lemma activeRoot_flat (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ) :
    backwardLog n (cavityTower T U l r) m (activeEnergy V x j l r z f)=
      backwardLog n (prod n T (pi n (fun i : Fin l => piTower n (fun a => U (rootArray l r i a))))) m
        (fun y => f (pathFst n y)+∑ i,mixedEnergy (rootArray l z i) (fun a => decide (a=j))
          (fun _ => V (pathFst n y))
          (fun a => x (rootArray l r i a) (pathMap (fun b : Ω × (Fin l → Fin p → Λ) => b.2 i a) n y))) := by
  rw [←backwardLog_of_projects n (cavityPack_projects T U l r)]
  congr 1
  funext y
  exact activeEnergy_pack V x j l r z f y

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonReplacement
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma successCount_le {p k : ℕ} [NeZero p] (a : Fin k → Fin p) : successCount a ≤ k := by
  unfold successCount
  apply (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin k))) =>
    show (if a i=0 then 1 else 0)≤1 by split_ifs <;> omega)).trans_eq
  simp

lemma successCount_cons {p k : ℕ} [NeZero p] (a : Fin p) (x : Fin k → Fin p) :
    successCount (Fin.cons a x)=(if a=0 then 1 else 0)+successCount x := by
  simp only [successCount,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma uniform_indicator_expect (p : ℕ) [NeZero p] (f : ℕ → ℝ) (n : ℕ) :
    (FiniteLaw.uniform : FiniteLaw (Fin p)).expect (fun a => f (n+if a=0 then 1 else 0)) =
      (f (n+1)+((p-1:ℕ):ℝ)*f n)/p := by
  classical
  rw [FiniteLaw.uniform_expect,Fintype.card_fin]
  congr 1
  have he (a : Fin p) : f (n+if a=0 then 1 else 0)=
      (if a=0 then f (n+1)-f n else 0)+f n := by split_ifs <;> simp
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]
  ring

/-- Finite independent replacement of real-or-null interactions by cavity
interactions. The error has its exact extensive coefficient. -/
lemma finite_count_replacement (p : ℕ) [NeZero p] (f : ℕ → ℕ → ℝ) (c : ℝ)
    (h : ∀ n l,f (n+1) l+((p-1:ℕ):ℝ)*f n l ≤ (p:ℝ)*(f n (l+1)-c))
    (k n l : ℕ) :
    (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (n+successCount a) l) ≤ f n (l+k)-(k:ℝ)*c := by
  induction k generalizing l with
  | zero => simp [FiniteLaw.expect,FiniteLaw.pi,successCount]
  | succ k ih =>
      rw [FiniteLaw.expect_pi_cons]
      simp only [successCount_cons]
      rw [FiniteLaw.expect_comm]
      calc
        _ ≤ (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
            (fun a => f (n+successCount a) (l+1)-c) := by
          apply FiniteLaw.expect_mono
          intro a
          have hn : ∀ b : Fin p,n+((if b=0 then 1 else 0)+successCount a)=
              (n+successCount a)+(if b=0 then 1 else 0) := by intro b; omega
          simp_rw [hn]
          rw [uniform_indicator_expect p (fun k => f k l)]
          exact (div_le_iff₀ (by exact_mod_cast NeZero.pos p)).mpr (by
            simpa only [mul_comm (p:ℝ)] using h (n+successCount a) l)
        _ ≤ f n ((l+1)+k)-(k:ℝ)*c-c := by
          rw [FiniteLaw.expect_sub,FiniteLaw.expect_const]
          exact sub_le_sub_right (ih (l+1)) c
        _ = _ := by rw [show (l+1)+k=l+(k+1) by omega,Nat.cast_add,Nat.cast_one]; ring

lemma integral_poisson_thinning (r : ℝ≥0) (p : ℕ) [NeZero p]
    (f : ℕ → ℝ) {B D : ℝ} (hD : 0≤D) (hf : ∀ n,|f n|≤B+D*n) :
    (∫ k,(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (successCount a)) ∂poissonMeasure r) =
    ∫ n,f n ∂poissonMeasure (r/p) := by
  let ν := fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p))
  have hi : Integrable (fun z : (k : ℕ) × (Fin k → Fin p) => f (successCount z.2))
      (familyLaw (poissonMeasure r) ν) := by
    apply familyLaw_integrable_bound (poissonMeasure r) ν
      (fun k (a : Fin k → Fin p) => f (successCount a)) (fun _ => measurable_of_countable _)
      ((integrable_const B).add ((poisson_integrable_count r).const_mul D))
    intro k a
    exact (hf _).trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (show (successCount a:ℝ)≤k by exact_mod_cast successCount_le a) hD) B)
  rw [← map_poisson_successCount r p]
  rw [integral_map (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCount a))).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [integral_familyLaw (poissonMeasure r) ν (fun k (a : Fin k → Fin p) => f (successCount a))
    (fun _ => measurable_of_countable _) hi]
  apply integral_congr_ae
  filter_upwards [] with k
  dsimp only [ν]
  rw [finiteUniform_pi,integral_finiteUniform]
  have hh : FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p))) =
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p)) := by
    apply FiniteLaw.ext
    intro a
    simp [FiniteLaw.pi,FiniteLaw.uniform]
  rw [hh,FiniteLaw.uniform_expect]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- Uniformized Poisson interpolation endpoint. The sole local input is the
conditional cavity replacement inequality, at ALL old real/cavity counts. -/
lemma poisson_count_replacement (r : ℝ≥0) (p : ℕ) [NeZero p]
    (f : ℕ → ℕ → ℝ) (c : ℝ) {B D : ℝ} (hD : 0≤D)
    (hf : ∀ n l,|f n l|≤B+D*(n+l))
    (h : ∀ n l,f (n+1) l+((p-1:ℕ):ℝ)*f n l ≤ (p:ℝ)*(f n (l+1)-c)) :
    (∫ n,f n 0 ∂poissonMeasure (r/p))+(r:ℝ)*c ≤ ∫ l,f 0 l ∂poissonMeasure r := by
  rw [← integral_poisson_thinning r p (fun n => f n 0) hD (by simpa using fun n => hf n 0)]
  have hb (k : ℕ) : |(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (successCount a) 0)|≤B+D*k := by
    apply FiniteLaw.abs_expect_le
    intro a
    exact (hf _ 0).trans (by simpa only [Nat.cast_zero,add_zero] using (add_le_add_right (mul_le_mul_of_nonneg_left (show (successCount a:ℝ)≤k by exact_mod_cast successCount_le a) hD) B))
  have hi := poisson_average_integrable r _ hb
  have hj := poisson_average_integrable r (fun k => f 0 k) (by simpa using fun k => hf 0 k)
  have hh := integral_mono hi (hj.sub ((poisson_integrable_count r).mul_const c))
    (fun k => by simpa only [zero_add,Pi.sub_apply] using finite_count_replacement p f c h k 0 0)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hj ((poisson_integrable_count r).mul_const c),integral_mul_const,poisson_mean] at hh
  linarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperCountMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [NeZero N] in
lemma measurable_datumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ) :
    Measurable (fun z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
      datumRoot T U V x m j f k l z.1 z.2) := by
  let F := fun z : (RootPath (InteractionSample p) k × RootPath (InteractionSample p) l) ×
      (RootPath (Fin p → Fin N) k × RootPath (Fin p → Fin N) l × RootPath (Fin p → R) l) =>
    cavityRoot T U V x m j l z.2.2.2 z.2.2.1 z.1.2 (realCountEnergy V k z.2.1 z.1.1 f)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    apply measurable_cavityRoot
    · exact measurable_snd
    · intro y
      apply measurable_const.add
      exact Finset.measurable_sum _ (fun a _ =>
        (measurable_pi_apply _).comp (measurable_fst.comp ((measurable_rootArray k a).comp measurable_fst)))
  exact hF.comp
    ((((measurable_rootMap Prod.fst measurable_fst k).comp measurable_fst).prodMk
      ((measurable_rootMap Prod.fst measurable_fst l).comp measurable_snd)).prodMk
      (((measurable_rootMap (fun a : UpperDatum p N R => a.2.1) measurable_snd.fst k).comp measurable_fst).prodMk
        (((measurable_rootMap (fun a : UpperDatum p N R => a.2.1) measurable_snd.fst l).comp measurable_snd).prodMk
          ((measurable_rootMap (fun a : UpperDatum p N R => a.2.2) measurable_snd.snd l).comp measurable_snd))))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperFreshLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [NeZero N] in
lemma realCountEnergy_succ (V : FinitePath Ω n → Fin N → Spin) (k : ℕ)
    (i : RootPath (Fin p → Fin N) k) (z : RootPath (InteractionSample p) k)
    (a : Fin p → Fin N) (θ : InteractionSample p) (f : FinitePath Ω n → ℝ) :
    realCountEnergy V (k+1) (a,i) (θ,z) f =
      realCountEnergy V k i z f+(fun y => θ.1 (fun j => V y (a j))) := by
  funext y
  simp only [realCountEnergy,Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ,Pi.add_apply]
  ring

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_real_succ (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    (a : UpperDatum p N R) :
    datumRoot T U V x m j f (k+1) l (a,z) w =
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l w)) m
        (fun y => cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
          (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
          (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f) y+
            a.1.1 (fun d => V (pathMap (cavityProject l) n y) (a.2.1 d))) := by
  unfold datumRoot
  simp only [rootMap,realCountEnergy_succ,cavityRoot]
  congr 1
  funext y
  exact cavityEnergy_add V x j l _ _ _ _ _ y


end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [NeZero N] in
lemma measurable_freshRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool) :
    Measurable (freshRoot T U V x m f sel) := by
  apply measurable_from_prod_countable_left
  intro b
  unfold freshRoot
  dsimp only
  apply KernelTower.measurable_backwardLog
  intro y
  exact measurable_const.add (measurable_mixedEnergy _ _ _)

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma freshRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool)
    (a : UpperDatum p N R) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |freshRoot T U V x m f sel a|≤B+‖a.1.1‖ := by
  apply backwardLog_bound n _ m hm
  intro y
  exact abs_add_le _ _ |>.trans (add_le_add (hf _) (mixedEnergy_bound a.1 sel _ _))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma freshRoot_true (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) (a : UpperDatum p N R) :
    freshRoot T U V x m f (fun _ => true) a =
      backwardLog n T m (fun y => f y+a.1.1 (fun d => V y (a.2.1 d))) := by
  unfold freshRoot mixedTreeEnergy
  simp only [mixedEnergy_true]
  exact backwardLog_prod_fst n T (piTower n (fun d : Fin p => U (a.2.2 d))) m
    (fun y => f y+a.1.1 (fun d => V y (a.2.1 d)))

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_fresh_true (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    (a : UpperDatum p N R) :
    freshRoot (cavityTower T U l (rootMap (fun a => a.2.2) l w)) U
      (fun y => V (pathMap (cavityProject l) n y)) x m
      (cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
        (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
        (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f))
      (fun _ => true) a = datumRoot T U V x m j f (k+1) l (a,z) w := by
  rw [freshRoot_true,datumRoot_real_succ]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_fresh_selected (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    (a : UpperDatum p N R) :
    freshRoot (cavityTower T U l (rootMap (fun a => a.2.2) l w)) U
      (fun y => V (pathMap (cavityProject l) n y)) x m
      (cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
        (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
        (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f))
      (fun d => decide (d=j)) a = datumRoot T U V x m j f k (l+1) z (a,w) := rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperRealEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators ENNReal

lemma FiniteLaw.uniform_asProbability {J : Type} [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    ((FiniteLaw.uniform : FiniteLaw J).asProbability id).toMeasure=finiteUniform J := by
  apply Measure.ext_of_singleton
  intro j
  rw [FiniteLaw.asProbability_id_singleton]
  change ENNReal.ofReal ((Fintype.card J : ℝ)⁻¹)=(PMF.uniformOfFintype J).toMeasure {j}
  rw [PMF.toMeasure_apply_singleton,PMF.uniformOfFintype_apply,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J))]
  · simp
  · exact measurableSet_singleton j


namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_real_projection (M : Model p) (Q : FiniteLaw R) :
    MeasurePreserving (fun a : UpperDatum p N R => (a.1,a.2.1))
      (upperDatumLaw M Q) (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))) := by
  unfold upperDatumLaw
  rw [FiniteLaw.pi_uniform,FiniteLaw.uniform_asProbability]
  exact (MeasurePreserving.id _).prod measurePreserving_fst

end PrescribedTree
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
lemma pi_pad {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : Ω) (n : ℕ) (T : ι → KernelTower Ω n) :
    pi (n+1) (fun i => pad a n (T i))=pad (fun _ : ι => a) n (pi n T) := by
  simp_rw [←piTower_eq_pi]
  exact piTower_pad a n T
omit [Fintype Ω] in
lemma pathMap_snd {Λ : Type} (n : ℕ) (y : FinitePath (Ω×Λ) n) :
    pathMap Prod.snd n y=pathSnd n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R]
omit [Fintype R] in
lemma activeRoot_site (a : Λ) (r : ℕ) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)=1)
    (q k : ℕ) (b : RootPath (Fin (q+1) → R) k) (z : RootPath (InteractionSample (q+1)) k) (h : ℝ) :
    backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k b) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k b z
        (fun y => h*spin (terminalState r y))) =
      backwardLog r (piTower r (fun c : Fin k×Fin q => U (rootArray k b c.1 c.2.castSucc)))
        (fun d => m d.castSucc) (fun y => siteLog (rootArray k z) h
          (fun c => x (rootArray k b c.1 c.2.castSucc)
            (pathMap (fun w : Fin k×Fin q → Λ => w c) r y))) := by
  rw [activeRoot_flat]
  simp_rw [piTower_pad a r]
  rw [pi_pad (fun _ : Fin (q+1) => a) r]
  let F := fun (s : Spin) (y : FinitePath (Fin k → Fin (q+1) → Λ) r) =>
    h*spin s+∑ i,message (rootArray k z i).1
      (fun j => x (rootArray k b i j.castSucc)
        (pathMap (fun w : Fin k → Fin (q+1) → Λ => w i j.castSucc) r y)) s
  have he : (fun y : FinitePath (Spin × (Fin k → Fin (q+1) → Λ)) (r+1) =>
      h*spin (terminalState r (pathFst (r+1) y))+
        ∑ i,mixedEnergy (rootArray k z i) (fun j => decide (j=Fin.last q))
          (fun _ => terminalState r (pathFst (r+1) y))
          (fun j => x (rootArray k b i j) (pathPrefix r
            (pathMap (fun w : Spin × (Fin k → Fin (q+1) → Λ) => w.2 i j) (r+1) y)))) =
      fun y => F (terminalState r (pathFst (r+1) y)) (pathPrefix r (pathSnd (r+1) y)) := by
    funext y
    simp only [mixedEnergy_last,F]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext j
    congr 1
    rw [pathMap_pathPrefix]
    rw [←pathMap_snd,←pathMap_comp]
    rfl
  rw [he,backwardLog_terminal_pad,hend]
  have hs (y : FinitePath (Fin k → Fin (q+1) → Λ) r) :
      (FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun s => F s y)=
      siteLog (rootArray k z) h (fun c : Fin k×Fin q => x (rootArray k b c.1 c.2.castSucc)
        (pathMap (fun w : Fin k → Fin (q+1) → Λ => w c.1 c.2.castSucc) r y)) := by
    simp only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.expect,
      FiniteLaw.uniform,Fintype.card_bool,Nat.cast_ofNat,inv_mul_eq_div,
      siteLog,F,Finset.sum_div]
  simp only [hs]
  rw [←backwardLog_of_projects r (pi_rect_castSucc_projects r k q (fun i j => U (rootArray k b i j)))]
  congr 1
  funext y
  congr 1
  funext c
  congr 1
  rw [←pathMap_comp]
  rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySiteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
namespace FiniteLaw
variable {R : Type} [Fintype R]
lemma expect_rect_castSucc (Q : FiniteLaw R) (k q : ℕ) (F : (Fin k×Fin q → R) → ℝ) :
    (pi (fun _ : Fin k => pi (fun _ : Fin (q+1) => Q))).expect
      (fun x => F (fun c => x c.1 c.2.castSucc))=
      (pi (fun _ : Fin k×Fin q => Q)).expect F := by
  apply (expect_pi_curry (fun (_ : Fin k) (_ : Fin (q+1)) => Q)
    (fun y : Fin k×Fin (q+1) → R => F (fun c => y (c.1,c.2.castSucc)))).trans
  exact expect_pi_injective (fun _ : Fin k×Fin (q+1) => Q)
    (fun z : Fin k×Fin q => (z.1,z.2.castSucc)) (by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun z : Fin k×Fin (q+1) => z.1) h
      · exact (Fin.castSucc_injective q) (congrArg (fun z : Fin k×Fin (q+1) => z.2) h)) F
end FiniteLaw
namespace PrescribedTree
open KernelTower
variable {Λ R : Type} [Fintype Λ] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
lemma activeRoot_site_mean (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)=1)
    (q k : ℕ) (z : RootPath (InteractionSample (q+1)) k) (h : ℝ) :
    (∫ b : RootPath (Fin (q+1) → R) k,backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k b) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k b z
        (fun y => h*spin (terminalState r y)))
      ∂rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog (rootArray k z) h) := by
  simp_rw [activeRoot_site a r U x m hend q k]
  let F := fun b : Fin k → Fin (q+1) → R =>
    backwardLog r (piTower r (fun c : Fin k×Fin q => U (b c.1 c.2.castSucc)))
      (fun d => m d.castSucc) (fun y => siteLog (rootArray k z) h
        (fun c => x (b c.1 c.2.castSucc) (pathMap (fun w : Fin k×Fin q → Λ => w c) r y)))
  change (∫ b,F (rootArray k b) ∂rootLaw k (fun _ =>
    ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=_
  rw [integral_rootArray_eq_pi _ k F]
  rw [FiniteLaw.integral_pi_asProbability]
  rw [finite_trialLog]
  exact FiniteLaw.expect_rect_castSucc Q k q (fun b =>
    backwardLog r (piTower r (fun c => U (b c))) (fun d => m d.castSucc)
      (fun y => siteLog (rootArray k z) h (fun c => x (b c) (pathMap (fun w : Fin k×Fin q → Λ => w c) r y))))
end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FirstMomentUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

lemma integrable_rootArray_sum {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Integrable g μ) (k : ℕ) :
    Integrable (fun z : RootPath X k => ∑ a,g (rootArray k z a)) (rootLaw k (fun _ => μ)) := by
  apply integrable_finsetSum
  intro a _
  simpa only [Function.comp_def, rootArrayEquiv_apply] using
    (measurePreserving_rootArray μ k).integrable_comp_of_integrable
      (integrable_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg)

lemma integral_rootArray_sum {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Integrable g μ) (k : ℕ) :
    (∫ z : RootPath X k,∑ a,g (rootArray k z a) ∂rootLaw k (fun _ => μ))=k*∫ x,g x ∂μ := by
  rw [integral_rootArray_eq_pi μ k (fun z => ∑ a,g (z a)),
    integral_finsetSum _ (fun a _ => integrable_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg)]
  have he (a : Fin k) : (∫ z : Fin k → X,g (z a) ∂Measure.pi (fun _ => μ))=∫ x,g x ∂μ :=
    integral_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg.aestronglyMeasurable
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

namespace PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_norm_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |datumRoot T U V x m j f k l z w|≤B+(∑ a,‖(rootArray k z a).1.1‖)+(∑ a,‖(rootArray l w a).1.1‖) := by
  have hbase (y : FinitePath Ω n) :
      |realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f y|≤B+∑ a,‖(rootArray k z a).1.1‖ := by
    apply (abs_add_le _ _).trans
    apply add_le_add (hf y)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun a _ => by simpa only [rootArray_rootMap,Real.norm_eq_abs] using norm_le_pi_norm (rootArray k z a).1.1 _)
  simpa only [rootArray_rootMap,datumRoot] using cavityRoot_bound T U V x m hm j l
    (rootMap (fun a => a.2.2) l w) (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w) _ hbase

omit [MeasurableSingletonClass R] in
lemma upperDatum_integrable_norm (M : Model p) (hM : Admissible M) (Q : FiniteLaw R) :
    Integrable (fun a : UpperDatum p N R => ‖a.1.1‖) (upperDatumLaw (N := N) M Q) :=
  measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable

lemma datumRoot_integrable_firstMoment (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    Integrable (fun z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
      datumRoot T U V x m j f k l z.1 z.2)
      ((rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) := by
  have hk := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) (fun a => ‖a.1.1‖) (upperDatum_integrable_norm M hM Q) k
  have hl := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) (fun a => ‖a.1.1‖) (upperDatum_integrable_norm M hM Q) l
  apply ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))).add (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q))) |>.mono'
    (measurable_datumRoot T U V x m j f k l).aestronglyMeasurable
  exact ae_of_all _ (fun z => datumRoot_norm_bound T U V x m hm j f k l z.1 z.2 hf)

lemma upperCountMean_bound_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |upperCountMean M T Q U V x m j f k l|≤B+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*(k+l) := by
  let g := fun a : UpperDatum p N R => ‖a.1.1‖
  have hg := upperDatum_integrable_norm (N := N) M hM Q
  have hk := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) g hg k
  have hl := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) g hg l
  have hB := ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))).add (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q)))
  unfold upperCountMean
  rw [← integral_prod _ (datumRoot_integrable_firstMoment M hM Q T U V x m hm j f k l hf)]
  apply (abs_integral_le_integral_abs).trans
  apply (integral_mono (datumRoot_integrable_firstMoment M hM Q T U V x m hm j f k l hf).abs hB
    (fun z => datumRoot_norm_bound T U V x m hm j f k l z.1 z.2 hf)).trans_eq
  change (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      (B + ∑ a, g (rootArray k z.1 a)) + ∑ a, g (rootArray l z.2 a)
      ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) = _
  have he1 := integral_add ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))) (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q)))
  have he2 := integral_add (integrable_const B) (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))
  simp only [Pi.add_apply] at he1 he2
  rw [he1,he2]
  have hek : (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      ∑ a,g (rootArray k z.1 a) ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod
        (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) =
      ∫ z : RootPath (UpperDatum p N R) k,∑ a,g (rootArray k z a) ∂rootLaw k (fun _ => upperDatumLaw (N := N) M Q) :=
    by simpa only [probReal_univ,one_smul] using (integral_fun_fst (μ := rootLaw k (fun _ => upperDatumLaw (N := N) M Q)) (ν := rootLaw l (fun _ => upperDatumLaw (N := N) M Q)) (fun z => ∑ a,g (rootArray k z a)))
  have hel : (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      ∑ a,g (rootArray l z.2 a) ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod
        (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) =
      ∫ z : RootPath (UpperDatum p N R) l,∑ a,g (rootArray l z a) ∂rootLaw l (fun _ => upperDatumLaw (N := N) M Q) :=
    by simpa only [probReal_univ,one_smul] using (integral_fun_snd (μ := rootLaw k (fun _ => upperDatumLaw (N := N) M Q)) (ν := rootLaw l (fun _ => upperDatumLaw (N := N) M Q)) (fun z => ∑ a,g (rootArray l z a)))
  rw [hek,hel,integral_rootArray_sum _ g hg k,integral_rootArray_sum _ g hg l]
  have he : (∫ a,g a ∂upperDatumLaw (N := N) M Q)=∫ a,‖a.1‖ ∂M.disorder.toMeasure := by
    simpa only [g,upperDatumLaw,probReal_univ,one_smul] using (integral_fun_fst (μ := M.disorder.toMeasure) (ν := ((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) (fun a : InteractionSample p => ‖a.1‖))
  rw [he]
  simp only [integral_const,probReal_univ,one_smul]
  ring

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalReservoirIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
lemma rootMap_selectRoot {X Y : Type} (f : X → Y) (l : ℕ) (b : RootPath Bool l) (z : RootPath X l) :
    rootMap f (selectedCount l b) (selectRoot l b z)=selectRoot l b (rootMap f l z) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · exact ih b z.2
    · exact Prod.ext rfl (ih b z.2)

namespace PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R X : Type} [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace X]
    {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma measurable_activeEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    Measurable (fun a => activeEnergy V x j l r (z a) f y) := by
  induction l with
  | zero => exact measurable_const
  | succ l ih =>
    apply (ih r.2 (fun a => (z a).2) (measurable_snd.comp hz) (pathFst n y)).add
    exact (measurable_mixedEnergy _ _ _).comp (measurable_fst.comp hz)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_bound (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |activeEnergy V x j l r z f y|≤B+∑ i,‖(rootArray l z i).1‖ := by
  induction l with
  | zero => simpa [activeEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    have h := add_le_add (ih r.2 z.2 (pathFst n y))
      (mixedEnergy_bound z.1 (fun a => decide (a=j))
        (fun _ => V (pathMap (cavityProject l) n (pathFst n y)))
        (fun a => x (r.1 a) (pathMap (fun b : Fin p → Λ => b a) n (pathSnd n y))))
    simpa only [singleBlockEnergy,Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ,add_assoc,add_comm,add_left_comm] using h

lemma measurable_activeDatumRoot [MeasurableSpace R] [MeasurableSingletonClass R]
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Measurable (activeDatumRoot T U V x m j f l) := by
  let F := fun z : RootPath (InteractionSample p) l × RootPath (Fin p → R) l =>
    backwardLog n (cavityTower T U l z.2) m (activeEnergy V x j l z.2 z.1 f)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    exact measurable_backwardLog n _ m (measurable_activeEnergy V x j l b id measurable_id f)
  exact hF.comp ((measurable_rootMap Prod.fst measurable_fst l).prodMk
    (measurable_rootMap Prod.snd measurable_snd l))

omit [NeZero N] in
lemma allocatedMean_selected [MeasurableSpace R] [MeasurableSingletonClass R]
    (M : Model p) (Q : FiniteLaw R) (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (s : Fin N) (l : ℕ)
    (c : RootPath (Fin N) l) :
    (∫ z : RootPath (InteractionSample p × (Fin p → R)) l,
      backwardLog n (cavityTower T U l (rootMap Prod.snd l z)) m
        (allocatedEnergy V x j s l (rootMap Prod.snd l z) c (rootMap Prod.fst l z) f)
      ∂rootLaw l (fun _ => M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure))=
    ∫ z,activeDatumRoot T U V x m j f (selectedCount l (rootMap (fun a => decide (a=s)) l c)) z
      ∂rootLaw (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        (fun _ => M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) := by
  simp_rw [allocatedRoot_selected,←rootMap_selectRoot]
  exact integral_selectRoot _ l _ _ (measurable_activeDatumRoot T U V x m j f _)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityDatumProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
lemma measurable_selectRoot {X : Type} [MeasurableSpace X] (l : ℕ) (b : RootPath Bool l) :
    Measurable (selectRoot (X := X) l b) := by
  induction l with
  | zero => exact measurable_id
  | succ l ih =>
    cases b with | mk a b =>
      cases a
      · exact (ih b).comp measurable_snd
      · exact measurable_fst.prodMk ((ih b).comp measurable_snd)
namespace PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_site_projection (M : Model p) (Q : FiniteLaw R) (j : Fin p) :
    MeasurePreserving (fun a : UpperDatum p N R => (a.2.1 j,(a.1,a.2.2)))
      (upperDatumLaw M Q) ((finiteUniform (Fin N)).prod
        (M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)) := by
  unfold upperDatumLaw
  rw [FiniteLaw.pi_uniform,FiniteLaw.uniform_asProbability,←finiteUniform_pi]
  exact ((measurePreserving_eval (fun _ : Fin p => finiteUniform (Fin N)) j).prod
    (MeasurePreserving.id _)).comp
    ((measurePreserving_prodAssoc _ _ _).comp
      (((Measure.measurePreserving_swap : MeasurePreserving Prod.swap
        (M.disorder.toMeasure.prod (Measure.pi (fun _ : Fin p => finiteUniform (Fin N))))
        ((Measure.pi (fun _ : Fin p => finiteUniform (Fin N))).prod M.disorder.toMeasure)).prod
        (MeasurePreserving.id _)).comp (MeasurePreserving.symm MeasurableEquiv.prodAssoc
          (measurePreserving_prodAssoc _ _ _))))

omit [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma allocatedEnergy_bound (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |allocatedEnergy V x j s l r c z f y|≤B+∑ i,‖(rootArray l z i).1‖ := by
  induction l with
  | zero => simpa [allocatedEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    have he : |if c.1=s then singleBlockEnergy V x j l r.1 z.1 y else 0|≤‖z.1.1‖ := by
      split_ifs
      · exact mixedEnergy_bound _ _ _ _
      · simp
    have h := add_le_add (ih r.2 c.2 z.2 (pathFst n y)) he
    simpa only [Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ,add_assoc,add_comm,add_left_comm] using h

omit [NeZero N] in
lemma measurable_allocatedDatumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (s : Fin N) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Measurable (fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
      allocatedDatumRoot T U V x m j s f l z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro c
  simp only [allocatedDatumRoot,allocatedRoot_selected,←rootMap_selectRoot]
  exact (measurable_activeDatumRoot T U V x m j f _).comp
    (measurable_selectRoot l (rootMap (fun a => decide (a=s)) l c))

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
lemma rootMap_comp {X Y Z : Type} (f : X → Y) (g : Y → Z) (k : ℕ) (z : RootPath X k) :
    rootMap g k (rootMap f k z)=rootMap (g ∘ f) k z := by
  induction k with
  | zero => rfl
  | succ k ih => exact Prod.ext rfl (ih z.2)

lemma measurePreserving_rootSplit {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] (k : ℕ) :
    MeasurePreserving (fun z : RootPath (X×Y) k => (rootMap Prod.fst k z,rootMap Prod.snd k z))
      (rootLaw k (fun _ => μ.prod ν)) ((rootLaw k (fun _ => μ)).prod (rootLaw k (fun _ => ν))) := by
  have h := ((MeasurePreserving.symm (rootArrayEquiv k) (measurePreserving_rootArray μ k)).prod
    (MeasurePreserving.symm (rootArrayEquiv k) (measurePreserving_rootArray ν k))).comp
    ((measurePreserving_arrowProdEquivProdArrow X Y (Fin k) (fun _ => μ) (fun _ => ν)).comp
      (measurePreserving_rootArray (μ.prod ν) k))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  apply Prod.ext
  · apply (rootArrayEquiv (X := X) k).injective
    dsimp only [Function.comp_apply,Prod.map,Prod.fst]
    rw [MeasurableEquiv.apply_symm_apply]
    funext i
    simp only [rootArrayEquiv_apply,rootArray_rootMap]
    rfl
  · apply (rootArrayEquiv (X := Y) k).injective
    dsimp only [Function.comp_apply,Prod.map,Prod.snd]
    rw [MeasurableEquiv.apply_symm_apply]
    funext i
    simp only [rootArrayEquiv_apply,rootArray_rootMap]
    rfl

lemma integral_rootSplit {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (k : ℕ) (F : RootPath X k × RootPath Y k → ℝ) (hF : Measurable F)
    (hi : Integrable F ((rootLaw k (fun _ => μ)).prod (rootLaw k (fun _ => ν)))) :
    (∫ z,F (rootMap Prod.fst k z,rootMap Prod.snd k z) ∂rootLaw k (fun _ => μ.prod ν))=
      ∫ x,∫ y,F (x,y) ∂rootLaw k (fun _ => ν) ∂rootLaw k (fun _ => μ) := by
  have hp := measurePreserving_rootSplit μ ν k
  rw [← integral_prod F hi,←hp.map_eq,
    integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityAllocatedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma allocatedDatumRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) (c : RootPath (Fin N) l)
    (z : RootPath (InteractionSample p × (Fin p → R)) l) :
    |allocatedDatumRoot T U V x m j s f l c z|≤‖f‖+∑ a,‖(rootArray l z a).1.1‖ := by
  apply backwardLog_bound n _ m hm
  intro y
  simpa only [rootArray_rootMap] using allocatedEnergy_bound V x j s l
    (rootMap Prod.snd l z) c (rootMap Prod.fst l z) f (fun w => norm_le_pi_norm f w) y

lemma allocatedDatumRoot_integrable (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Integrable (fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
      allocatedDatumRoot T U V x m j s f l z.1 z.2)
      ((rootLaw l (fun _ => finiteUniform (Fin N))).prod
        (rootLaw l (fun _ => M.disorder.toMeasure.prod
          ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure))) := by
  have hi : Integrable (fun z : InteractionSample p × (Fin p → R) => ‖z.1.1‖)
      (M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) :=
    measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable
  apply ((integrable_const ‖f‖).add ((integrable_rootArray_sum _ _ hi l).comp_snd
    (rootLaw l (fun _ => finiteUniform (Fin N))))).mono'
    (measurable_allocatedDatumRoot T U V x m j s f l).aestronglyMeasurable
  exact ae_of_all _ (fun z => allocatedDatumRoot_bound T U V x m hm j s f l z.1 z.2)

lemma upperAllocatedMean (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    (∫ z : RootPath (UpperDatum p N R) l,
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f)
        ∂rootLaw l (fun _ => upperDatumLaw M Q))=
      ∫ c,activeCountMean M Q T U V x m j f
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N)) := by
  let F := fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
    allocatedDatumRoot T U V x m j s f l z.1 z.2
  have hFm := measurable_allocatedDatumRoot T U V x m j s f l
  have he : (fun z : RootPath (UpperDatum p N R) l =>
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f))=
      fun z => F (rootMap Prod.fst l (rootMap (fun a => (a.2.1 j,(a.1,a.2.2))) l z),
        rootMap Prod.snd l (rootMap (fun a => (a.2.1 j,(a.1,a.2.2))) l z)) := by
    funext z
    simp only [F,allocatedDatumRoot,rootMap_comp,Function.comp_def]
  rw [he]
  apply (integral_rootMap (upperDatum_site_projection M Q j) l
    (fun z => F (rootMap Prod.fst l z,rootMap Prod.snd l z))
    (hFm.comp ((measurable_rootMap Prod.fst measurable_fst l).prodMk
      (measurable_rootMap Prod.snd measurable_snd l)))).trans
  rw [integral_rootSplit _ _ l F hFm (allocatedDatumRoot_integrable M hM Q T U V x m hm j s f l)]
  apply integral_congr_ae
  filter_upwards [] with c
  exact allocatedMean_selected M Q T U V x m j f s l c

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FirstMomentFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
lemma integral_root_prod_finite_integrable {X J : Type} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin n → X) × (Fin n → J) → ℝ) (_hF : Measurable F)
    (hi : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => finiteUniform J)))) :
    (∫ z : RootPath (X×J) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod (finiteUniform J))) =
      ∫ x : Fin n → X,(FiniteLaw.uniform : FiniteLaw (Fin n → J)).expect (fun j => F (x,j))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_root_prod μ (finiteUniform J) n F hi]
  simp only [finiteUniform_pi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_finiteUniform,FiniteLaw.expect_uniform]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
namespace PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]
omit [MeasurableSingletonClass R] in
lemma upperCountMean_real_firstMoment (M : Model p) (hM : Admissible M) (T : KernelTower Ω n) (Q : FiniteLaw R)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (hm : ∀ d,0 < m d)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k : ℕ) :
    upperCountMean M T Q U V x m j f k 0 =
      ∫ z : Fin k → InteractionSample p,
       (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
        (fun i => backwardLog n T m (fun y => f y+∑ a,(z a).1 (fun b => V y (i a b))))
          ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F : RootPath (InteractionSample p × (Fin p → Fin N)) k → ℝ := fun z =>
    backwardLog n T m (fun y => f y+∑ a,(rootArray k z a).1.1 (fun b => V y ((rootArray k z a).2 b)))
  have hFm : Measurable F := by
    apply measurable_backwardLog
    intro y
    apply measurable_const.add
    apply Finset.measurable_sum
    intro a _
    exact (measurable_pi_apply (V y)).comp ((PhysicalRoot.measurable_indexedPotential (fun x : InteractionSample p => x)
      (fun σ => (measurable_pi_apply σ).comp measurable_fst)).comp (measurable_rootArray k a))
  have he : upperCountMean M T Q U V x m j f k 0 =
      ∫ z,F (rootMap (fun a : UpperDatum p N R => (a.1,a.2.1)) k z)
        ∂rootLaw k (fun _ => upperDatumLaw M Q) := by
    let : IsProbabilityMeasure (rootLaw 0 (fun _ : Fin 0 => upperDatumLaw (N := N) M Q)) := Measure.dirac.isProbabilityMeasure
    unfold upperCountMean
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [datumRoot,cavityRoot,cavityTower,cavityEnergy,realCountEnergy,
      rootArray_rootMap,F]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    rfl
  rw [he,integral_rootMap (upperDatum_real_projection M Q) k F hFm]
  apply integral_root_prod_finite_integrable M.disorder.toMeasure k
    (fun z : (Fin k → InteractionSample p) × (Fin k → Fin p → Fin N) => backwardLog n T m (fun y => f y+∑ a,(z.1 a).1 (fun b => V y (z.2 a b))))
  · apply measurable_from_prod_countable_left
    intro i
    apply measurable_backwardLog
    intro y
    change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
    exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
      (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
  · apply ((integrable_const ‖f‖).add ((integrable_finsetSum Finset.univ
        (fun (a : Fin k) _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) (i := a)
          hM.interaction_integrable)).comp_fst (Measure.pi (fun _ : Fin k => finiteUniform (Fin p → Fin N))))).mono'
    · apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_left
      intro i
      apply measurable_backwardLog
      intro y
      change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
      exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
        (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
    · exact ae_of_all _ (fun z => backwardLog_bound n T m hm (fun y =>
        (abs_add_le _ _).trans (add_le_add (norm_le_pi_norm f y)
          ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum (fun a _ => norm_le_pi_norm (z.1 a).1 _))))))

end PrescribedTree
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma integral_upperDatumLaw_integrable (M : Model p) (Q : FiniteLaw R)
    (g : UpperDatum p N R → ℝ) (hg : Measurable g) (hi : Integrable g (upperDatumLaw M Q)) :
    (∫ a,g a ∂upperDatumLaw M Q) =
      ∫ z,(FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
        (fun i => (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r => g (z,i,r))) ∂M.disorder.toMeasure := by
  rw [upperDatumLaw,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  have hiz : Integrable (fun a : (Fin p → Fin N) × (Fin p → R) => g (z,a))
      (((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod
        ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) :=
    Integrable.of_bound (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ‖fun a : (Fin p → Fin N) × (Fin p → R) => g (z,a)‖
      (ae_of_all _ (fun a => norm_le_pi_norm (fun a => g (z,a)) a))
  rw [integral_prod _ hiz]
  rw [FiniteLaw.integral_asProbability]
  apply FiniteLaw.expect_congr
  intro i
  exact FiniteLaw.integral_asProbability _ _ _

lemma freshRoot_mean_sub_firstMoment (M : Model p) (hM : Admissible M)
    (Q : FiniteLaw R) (T : KernelTower Ω n)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin (n+1) → ℝ) (hm : ∀ d : Fin n,0 < m d.succ)
    (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool) {B : ℝ}
    (hf : ∀ y,|f y|≤B) :
    (∫ a,freshRoot T U V x (fun d => m d.succ) f sel a ∂upperDatumLaw M Q)-
      backwardLog n T (fun d => m d.succ) f =
      ∫ θ,mixedRootIncrement T Q U V x m f θ sel ∂M.disorder.toMeasure := by
  let g := freshRoot T U V x (fun d => m d.succ) f sel
  have hg := measurable_freshRoot T U V x (fun d => m d.succ) f sel
  have hb (a : InteractionSample p) (i : Fin p → Fin N) (r : Fin p → R) : |g (a,i,r)|≤B+‖a.1‖ :=
    freshRoot_bound T U V x _ hm f sel (a,i,r) hf
  have hi : Integrable g (upperDatumLaw M Q) := by
    apply ((integrable_const B).add (upperDatum_integrable_norm M hM Q)).mono' hg.aestronglyMeasurable
    exact ae_of_all _ (fun a => hb a.1 a.2.1 a.2.2)
  rw [integral_upperDatumLaw_integrable M Q g hg hi]
  let G := fun θ => (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
    (fun i => (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r => g (θ,i,r)))
  have hG : Measurable G := FiniteLaw.measurable_expect _ (fun i =>
    FiniteLaw.measurable_expect _ (fun r => hg.comp (measurable_id.prodMk measurable_const)))
  have hiG : Integrable G M.disorder.toMeasure := by
    apply ((integrable_const B).add hM.interaction_integrable).mono' hG.aestronglyMeasurable
    exact ae_of_all _ (fun a => FiniteLaw.abs_expect_le _ (fun i => FiniteLaw.abs_expect_le _ (hb a i)))
  change (∫ θ,G θ ∂M.disorder.toMeasure)-_=_
  have hc : backwardLog n T (fun d => m d.succ) f =
      ∫ _θ : InteractionSample p, backwardLog n T (fun d => m d.succ) f ∂M.disorder.toMeasure := by simp
  rw [hc,← integral_sub hiG (integrable_const _)]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [mixedRootIncrement,FiniteLaw.expect_sub,FiniteLaw.expect_const]
  rfl

lemma freshRoot_replacement_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) {B : ℝ}
    (hf : ∀ y,|f y|≤B) :
    (∫ a,freshRoot T U V x (fun d => m d.succ) f (fun _ => true) a ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*backwardLog n T (fun d => m d.succ) f ≤
      (p:ℝ)*(∫ a,freshRoot T U V x (fun d => m d.succ) f (fun d => decide (d=j)) a ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  have h := integral_mixedRoot_combination_nonpos M hM T Q U V x m hm hpos hstrict hroot hend f j
  simp_rw [mixedRootIncrement_false] at h
  rw [← freshRoot_mean_sub_firstMoment M hM Q T U V x m hstrict f (fun _ => true) hf,
    ← freshRoot_mean_sub_firstMoment M hM Q T U V x m hstrict f (fun d => decide (d=j)) hf] at h
  have hp : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by have := hM.arity; omega : 1≤p),Nat.cast_one]
  rw [hp] at h ⊢
  nlinarith

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FirstMomentConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma datumRoot_conditional_replacement_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    :
    (∫ a,datumRoot T U V x (fun d => m d.succ) j f (k+1) l (a,z) w ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*datumRoot T U V x (fun d => m d.succ) j f k l z w ≤
      (p:ℝ)*(∫ a,datumRoot T U V x (fun d => m d.succ) j f k (l+1) z (a,w) ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  let F := cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
        (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
        (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f)
  have h := freshRoot_replacement_firstMoment M hM
    (cavityTower T U l (rootMap (fun a => a.2.2) l w)) Q U
    (fun y => V (pathMap (cavityProject l) n y)) x m hm hpos hstrict hroot hend F j
    (fun y => norm_le_pi_norm F y)
  dsimp only [F] at h
  simp only [datumRoot_fresh_true,datumRoot_fresh_selected] at h
  exact h

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FirstMomentCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperCountMean_replacement_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    :
    upperCountMean M T Q U V x (fun d => m d.succ) j f (k+1) l+
      ((p-1:ℕ):ℝ)*upperCountMean M T Q U V x (fun d => m d.succ) j f k l ≤
      (p:ℝ)*upperCountMean M T Q U V x (fun d => m d.succ) j f k (l+1)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  let D := upperDatumLaw (N := N) M Q
  let μ := rootLaw k (fun _ => D)
  let ν := rootLaw l (fun _ => D)
  let F := fun zw : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
    datumRoot T U V x (fun d => m d.succ) j f k l zw.1 zw.2
  let G := fun azw : (UpperDatum p N R × RootPath (UpperDatum p N R) k) × RootPath (UpperDatum p N R) l =>
    datumRoot T U V x (fun d => m d.succ) j f (k+1) l azw.1 azw.2
  let H := fun zaw : RootPath (UpperDatum p N R) k × (UpperDatum p N R × RootPath (UpperDatum p N R) l) =>
    datumRoot T U V x (fun d => m d.succ) j f k (l+1) zaw.1 zaw.2
  have hF : Integrable F (μ.prod ν) :=
    datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f k l (fun y => norm_le_pi_norm f y)
  have hG : Integrable G ((D.prod μ).prod ν) :=
    datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f (k+1) l (fun y => norm_le_pi_norm f y)
  have hH : Integrable H (μ.prod (D.prod ν)) :=
    datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f k (l+1) (fun y => norm_le_pi_norm f y)
  have ig := integrable_triple_rotate D μ ν G hG
  have ih := integrable_triple_middle_swap μ D ν H hH
  let e := ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure)
  have hg := integral_mono (ig.add (hF.const_mul ((p-1:ℕ):ℝ))) ((ih.const_mul p).sub (integrable_const e))
    (fun zw => datumRoot_conditional_replacement_firstMoment M hM T Q U V x m hm hpos hstrict hroot hend j f k l zw.1 zw.2)
  simp only [Pi.add_apply,Pi.sub_apply] at hg
  rw [integral_add ig (hF.const_mul _),integral_sub (ih.const_mul _) (integrable_const e),
    integral_const_mul,integral_const_mul] at hg
  have he : ∫ _zw,e ∂μ.prod ν=e := by
    have := rootLawProbability k (fun _ => D)
    have := rootLawProbability l (fun _ => D)
    simp
  rw [he,integral_prod _ ig,integral_prod _ ih,integral_prod _ hF,
    ← integral_triple_rotate D μ ν G hG,← integral_triple_middle_swap μ D ν H hH] at hg
  exact hg

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityEndpointCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperAllocated_integrable (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Integrable (fun z : RootPath (UpperDatum p N R) l =>
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f))
      (rootLaw l (fun _ => upperDatumLaw M Q)) := by
  have h := ((measurePreserving_rootSplit _ _ l).comp
    (measurePreserving_rootMap (upperDatum_site_projection M Q j) l)).integrable_comp_of_integrable
      (allocatedDatumRoot_integrable M hM Q T U V x m hm j s f l)
  simpa only [Function.comp_def,allocatedDatumRoot,rootMap_comp] using h

omit [MeasurableSingletonClass R] in
lemma upperCountMean_cavity (M : Model p) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    upperCountMean M T Q U V x m j f 0 l=
      ∫ z : RootPath (UpperDatum p N R) l,
        cavityRoot T U V x m j l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1) l z) (rootMap Prod.fst l z) f
        ∂rootLaw l (fun _ => upperDatumLaw M Q) := by
  unfold upperCountMean datumRoot realCountEnergy
  simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  change (∫ _ : Unit, _ ∂Measure.dirac ())=_
  simp only [integral_dirac]

lemma upperCountMean_separable (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (l : ℕ) :
    upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l=
      ∑ s : Fin N,∫ c,activeCountMean M Q (T s) U (V s) x m j (f s)
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N)) := by
  rw [upperCountMean_cavity]
  simp_rw [cavityRoot_separable,rootMap_comp,Function.comp_def]
  rw [integral_finsetSum _ (fun s _ => upperAllocated_integrable M hM Q (T s) U (V s) x m hm j s (f s) l)]
  exact Finset.sum_congr rfl (fun s _ => upperAllocatedMean M hM Q (T s) U (V s) x m hm j s (f s) l)

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p : ℕ}

lemma activeCountMean_bound (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : FinitePath Ω n → ℝ) (l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |activeCountMean M Q T U V x m j f l|≤B+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*l := by
  let ν := M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure
  have hi : Integrable (fun z : InteractionSample p × (Fin p → R) => ‖z.1.1‖) ν :=
    measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable
  have hs := integrable_rootArray_sum ν (fun z => ‖z.1.1‖) hi l
  have hB (z : RootPath (InteractionSample p × (Fin p → R)) l) :
      |activeDatumRoot T U V x m j f l z|≤B+∑ i,‖(rootArray l z i).1.1‖ := by
    apply backwardLog_bound n _ m hm
    intro y
    simpa only [rootArray_rootMap] using activeEnergy_bound V x j l
      (rootMap Prod.snd l z) (rootMap Prod.fst l z) f hf y
  have hF : Integrable (activeDatumRoot T U V x m j f l) (rootLaw l (fun _ => ν)) :=
    ((integrable_const B).add hs).mono'
      (measurable_activeDatumRoot T U V x m j f l).aestronglyMeasurable (ae_of_all _ hB)
  unfold activeCountMean
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hF.abs ((integrable_const B).add hs) hB).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const B) hs,integral_rootArray_sum ν _ hi l]
  have he : (∫ a : InteractionSample p × (Fin p → R),‖a.1.1‖ ∂ν)=
      ∫ a : InteractionSample p,‖a.1‖ ∂M.disorder.toMeasure := by
    simpa only [ν,probReal_univ,one_smul] using
      (integral_fun_fst (μ := M.disorder.toMeasure)
        (ν := ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)
        (fun a : InteractionSample p => ‖a.1‖))
  rw [he]
  simp only [integral_const,probReal_univ,one_smul,mul_comm]

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped NNReal
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperPoissonCount_bound_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (r : ℝ≥0)
    :
    (∫ k,upperCountMean M T Q U V x (fun d => m d.succ) j f k 0 ∂poissonMeasure (r/p))+
      (r:ℝ)*(((p-1:ℕ):ℝ)/p)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) ≤
    ∫ l,upperCountMean M T Q U V x (fun d => m d.succ) j f 0 l ∂poissonMeasure r := by
  have hp : 0 < p := by have := hM.arity; omega
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hpR : (p:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hp
  let e := ∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure
  have hh := poisson_count_replacement r p
    (upperCountMean M T Q U V x (fun d => m d.succ) j f)
    ((((p-1:ℕ):ℝ)/p)*e) (show 0 ≤ ∫ a : InteractionSample p, ‖a.1‖ ∂M.disorder.toMeasure from
      integral_nonneg (fun a => norm_nonneg a.1))
    (fun k l => upperCountMean_bound_firstMoment M hM T Q U V x _ hstrict j f k l
      (fun y => norm_le_pi_norm f y))
    (fun k l => ?_)
  · simpa only [mul_assoc] using hh
  · have h := upperCountMean_replacement_firstMoment M hM T Q U V x m hm hpos hstrict hroot hend j f k l
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [e]
    field_simp

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityInsertionFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]

lemma activeCountMean_site (q : ℕ) (M : Model (q+1)) (hM : Admissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last r)=1) (k : ℕ) (h : ℝ) :
    activeCountMean M Q (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
      (fun b => pad a r (U b)) (terminalState r)
      (fun b y => x b (pathPrefix r y)) m (Fin.last q)
      (fun y => h*spin (terminalState r y)) k=
    ∫ z : Fin k → InteractionSample (q+1),
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog z h)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F := fun z : RootPath (InteractionSample (q+1)) k × RootPath (Fin (q+1) → R) k =>
    backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k z.2) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k z.2 z.1
        (fun y => h*spin (terminalState r y)))
  have hFm : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    exact measurable_backwardLog (r+1) _ m (measurable_activeEnergy (terminalState r)
      (fun b y => x b (pathPrefix r y)) (Fin.last q) k b id measurable_id
      (fun y => h*spin (terminalState r y)))
  have hB (z : RootPath (InteractionSample (q+1)) k × RootPath (Fin (q+1) → R) k) :
      |F z|≤|h|+∑ i,‖(rootArray k z.1 i).1‖ := by
    apply backwardLog_bound _ _ _ hm
    intro y
    apply activeEnergy_bound _ _ _ _ _ _ _ _ y
    intro y
    simp only [abs_mul,abs_spin,mul_one]
    exact le_refl _
  have hi : Integrable F ((rootLaw k (fun _ => M.disorder.toMeasure)).prod
      (rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))) := by
    exact ((integrable_const |h|).add ((integrable_rootArray_sum M.disorder.toMeasure
      (fun a => ‖a.1‖) hM.interaction_integrable k).comp_fst _)).mono'
        hFm.aestronglyMeasurable (ae_of_all _ hB)
  unfold activeCountMean activeDatumRoot
  change (∫ z,F (rootMap Prod.fst k z,rootMap Prod.snd k z) ∂rootLaw k (fun _ => _))=_
  rw [integral_rootSplit _ _ k F hFm hi]
  have he (z : RootPath (InteractionSample (q+1)) k) :
      (∫ b,F (z,b) ∂rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog (rootArray k z) h) :=
    activeRoot_site_mean a r Q U x m hend q k z h
  simp only [he]
  exact integral_rootArray_eq_pi M.disorder.toMeasure k
    (fun z : Fin k → InteractionSample (q+1) =>
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog z h))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonSiteThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

/-- Poisson thinning for independent uniform categorical choices. -/
lemma compoundPoisson_uniform_indicator_at (r : ℝ≥0) (p : ℕ) [NeZero p] (s : Fin p) :
    compoundPoisson r (Measure.map (fun a : Fin p => if a=s then (1:ℝ) else 0)
      (finiteUniform (Fin p))) = compoundPoisson (r/p) (Measure.dirac (1:ℝ)) := by
  classical
  haveI : IsProbabilityMeasure (Measure.map (fun a : Fin p => if a=s then (1:ℝ) else 0) (finiteUniform (Fin p))) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_compoundPoisson,charFunDual_compoundPoisson]
  congr 1
  rw [charFunDual_apply,integral_map (measurable_of_countable _).aemeasurable (by fun_prop),
    integral_finiteUniform,charFunDual_apply,integral_dirac]
  have hp : (p:ℂ)≠0 := by exact_mod_cast (NeZero.ne p)
  have hs : (∑ a : Fin p,Complex.exp ((L (if a=s then (1:ℝ) else 0):ℂ)*Complex.I)) =
      Complex.exp ((L 1:ℂ)*Complex.I)+(p-1:ℕ) := by
    have he (a : Fin p) : Complex.exp ((L (if a=s then (1:ℝ) else 0):ℂ)*Complex.I)=
        (if a=s then Complex.exp ((L 1:ℂ)*Complex.I)-1 else 0)+1 := by
      split_ifs <;> simp
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hpn : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]
    rw [hpn]; ring
  rw [hs]
  simp only [Fintype.card_fin,NNReal.coe_div,NNReal.coe_natCast,Complex.ofReal_div,Complex.ofReal_natCast,Complex.real_smul,Complex.ofReal_inv]
  rw [show ((p-1:ℕ):ℂ)=(p:ℂ)-1 by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]]
  field_simp
  ring

lemma map_poisson_successCountAt (r : ℝ≥0) (p : ℕ) [NeZero p] (s : Fin p) :
    Measure.map (fun z : (k : ℕ) × (Fin k → Fin p) => successCountAt s z.2)
      (familyLaw (poissonMeasure r) (fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p)))) =
      poissonMeasure (r/p) := by
  classical
  have he : MeasurableEmbedding (fun n : ℕ => (n:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).measurableEmbedding Nat.cast_injective
  apply he.map_injective
  rw [Measure.map_map (measurable_of_countable _) (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCountAt s a))),
    ← compoundPoisson_dirac_one,← compoundPoisson_uniform_indicator_at r p s]
  simp only [Function.comp_def]
  rw [map_familyLaw_sum _ _ (fun k (a : Fin k → Fin p) => (successCountAt s a:ℝ))
    (fun k => measurable_of_countable _)]
  unfold compoundPoisson
  congr 1
  funext k
  rw [poissonMeasure_singleton,← Measure.pi_map_pi (fun _ : Fin k => (measurable_of_countable
    (fun a : Fin p => if a=s then (1:ℝ) else 0)).aemeasurable),
    Measure.map_map (by fun_prop) (measurable_of_countable _)]
  congr 2
  funext a
  simp [successCountAt]

lemma selectedCount_eq_successCountAt {p : ℕ} [NeZero p] (s : Fin p) (k : ℕ)
    (c : RootPath (Fin p) k) :
    selectedCount k (rootMap (fun a => decide (a=s)) k c)=successCountAt s (rootArray k c) := by
  induction k with
  | zero => simp [selectedCount,successCountAt]
  | succ k ih =>
    simp only [rootMap,successCountAt,Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ]
    split_ifs with h
    · simp [h,selectedCount,ih,successCountAt,Nat.add_comm]
    · simp [h,selectedCount,ih,successCountAt]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonRootSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
lemma successCountAt_le {p k : ℕ} [NeZero p] (s : Fin p) (a : Fin k → Fin p) :
    successCountAt s a≤k := by
  unfold successCountAt
  apply (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin k))) =>
    show (if a i=s then 1 else 0)≤1 by split_ifs <;> omega)).trans_eq
  simp

lemma integral_poisson_rootSelection (r : ℝ≥0) (N : ℕ) [NeZero N] (s : Fin N)
    (f : ℕ → ℝ) {B D : ℝ} (hD : 0≤D) (hf : ∀ n,|f n|≤B+D*n) :
    (∫ k,∫ c,f (selectedCount k (rootMap (fun a => decide (a=s)) k c))
      ∂rootLaw k (fun _ => finiteUniform (Fin N)) ∂poissonMeasure r)=
      ∫ n,f n ∂poissonMeasure (r/N) := by
  let ν := fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin N))
  have hi : Integrable (fun z : (k : ℕ) × (Fin k → Fin N) => f (successCountAt s z.2))
      (familyLaw (poissonMeasure r) ν) := by
    apply familyLaw_integrable_bound (poissonMeasure r) ν
      (fun k (a : Fin k → Fin N) => f (successCountAt s a)) (fun _ => measurable_of_countable _)
      ((integrable_const B).add ((poisson_integrable_count r).const_mul D))
    intro k a
    exact (hf _).trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (show (successCountAt s a:ℝ)≤k by exact_mod_cast successCountAt_le s a) hD) B)
  rw [←map_poisson_successCountAt r N s,
    integral_map (measurable_sigmaUncurry (fun k => measurable_of_countable
      (fun a : Fin k → Fin N => successCountAt s a))).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable,
    integral_familyLaw (poissonMeasure r) ν (fun k (a : Fin k → Fin N) => f (successCountAt s a))
      (fun _ => measurable_of_countable _) hi]
  apply integral_congr_ae
  filter_upwards [] with k
  simp_rw [selectedCount_eq_successCountAt]
  exact integral_rootArray_eq_pi _ k (fun c => f (successCountAt s c))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityPoissonEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped BigOperators NNReal
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperSelectedCountMean_bound (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    |∫ c,activeCountMean M Q T U V x m j f
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N))|≤
      ‖f‖+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*l := by
  apply abs_integral_le_bound_ae
  apply ae_of_all
  intro c
  apply (activeCountMean_bound M hM Q T U V x m hm j f _ (fun y => norm_le_pi_norm f y)).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun a => norm_nonneg a.1))
  rw [selectedCount_eq_successCountAt]
  exact_mod_cast successCountAt_le s (rootArray l c)

lemma upperPoisson_cavity_separable (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (r : ℝ≥0) :
    (∫ l,upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l ∂poissonMeasure r)=
      ∑ s : Fin N,∫ k,activeCountMean M Q (T s) U (V s) x m j (f s) k
        ∂poissonMeasure (r/N) := by
  simp_rw [upperCountMean_separable M hM Q T U V x m hm j f]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    exact integral_poisson_rootSelection r N s _ (integral_nonneg (fun a : InteractionSample p => norm_nonneg a.1))
      (fun l => activeCountMean_bound M hM Q (T s) U (V s) x m hm j (f s) l
        (fun y => norm_le_pi_norm (f s) y))
  · intro s _
    apply ((integrable_const ‖f s‖).add ((poisson_integrable_count r).const_mul
      (∫ a,‖a.1‖ ∂M.disorder.toMeasure))).mono' (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun l => upperSelectedCountMean_bound M hM Q (T s) U (V s) x m hm j s (f s) l)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExtendedExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
lemma snoc_exponents_pos {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    ∀ i : Fin (r+1),0 < Fin.snoc (α := fun _ => ℝ) m (1:ℝ) i := by
  intro i
  exact Fin.lastCases (by simp) (fun j => by simpa using (hm.2 j).1) i
lemma snoc_exponents_mono {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    Monotone (Fin.snoc (α := fun _ => ℝ) m (1:ℝ)) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    simpa only [Fin.snoc_last] using
      (Fin.lastCases (by simp) (fun a => by simpa using (hm.2 a).2.le) i : Fin.snoc (α := fun _ => ℝ) m (1:ℝ) i≤1)
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last j)) hij)
    | cast i =>
      simpa only [Fin.snoc_castSucc] using hm.1.monotone (show i≤j from hij)
lemma cons_snoc_exponents_mono {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    Monotone (Fin.cons (α := fun _ => ℝ) (0:ℝ) (Fin.snoc (α := fun _ => ℝ) m (1:ℝ))) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact le_refl _
    | succ j => simpa using (snoc_exponents_pos hm j).le
  | succ i =>
    induction j using Fin.cases with
    | zero => exact False.elim ((not_le_of_gt (Fin.succ_pos i)) hij)
    | succ j =>
      simpa only [Fin.cons_succ] using snoc_exponents_mono hm (show i≤j from Fin.succ_le_succ_iff.mp hij)
lemma cons_snoc_exponents_nonneg {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    ∀ i,0 ≤ Fin.cons (α := fun _ => ℝ) (0:ℝ) (Fin.snoc (α := fun _ => ℝ) m (1:ℝ)) i := by
  intro i
  exact Fin.cases (by simp) (fun j => by simpa using (snoc_exponents_pos hm j).le) i
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalPiRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]
lemma backwardLog_pi_terminal (a : ι → Ω) (P : ι → FiniteLaw Ω) (r : ℕ)
    (m : Fin (r+1) → ℝ) (hm : ∀ d,m d≠0) (f : (ι → Ω) → ℝ) :
    backwardLog (r+1) (pi (r+1) (fun i => terminalTower (a i) (P i) r)) m
      (fun y => f (fun i => terminalState r (FinitePath.proj (r+1) y i)))=
      (FiniteLaw.pi P).logMean (m (Fin.last r)) f := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (FiniteLaw.pi (fun i => FiniteLaw.point (a i))).logMean (m 0)
      (fun _ => backwardLog (r+1) (pi (r+1) (fun i => terminalTower (a i) (P i) r))
        (fun d => m d.succ) (fun y => f (fun i => terminalState r (FinitePath.proj (r+1) y i))))=_
    rw [ih (fun d => m d.succ) (fun d => hm d.succ)]
    exact FiniteLaw.logMean_const _ (hm 0) _
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {p N : ℕ} [NeZero N]
omit [MeasurableSingletonClass R] in
lemma upperCountMean_real_terminal (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (r : ℕ) (U : R → KernelTower Λ (r+1)) (x : R → FinitePath Λ (r+1) → ℝ)
    (m : Fin (r+1) → ℝ) (hm : ∀ d,0 < m d) (hend : m (Fin.last r)=1)
    (j : Fin p) (h : Fin N → ℝ) (k : ℕ) :
    upperCountMean M (KernelTower.pi (r+1) (fun _ : Fin N =>
      terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)) Q U
      (fun y s => terminalState r (FinitePath.proj (r+1) y s)) x m j
      (fun y => ∑ s,h s*spin (terminalState r (FinitePath.proj (r+1) y s))) k 0=
      ∫ z : Fin k → InteractionSample p,
        (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
          (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  rw [upperCountMean_real_firstMoment M hM]
  · apply integral_congr_ae
    filter_upwards [] with z
    apply FiniteLaw.expect_congr
    intro i
    rw [backwardLog_pi_terminal (fun _ : Fin N => false)
      (fun _ => (FiniteLaw.uniform : FiniteLaw Spin)) r m (fun d => (hm d).ne')
      (fun σ => (∑ s,h s*spin (σ s))+∑ a,(z a).1 (fun b => σ (i a b))),hend,FiniteLaw.pi_uniform,
      FiniteLaw.logMean_uniform]
    unfold logPartition
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      unfold logWeight
      ring
    · simp [Real.log_pow]
  · exact hm
end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityGapFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped BigOperators NNReal
variable {Λ R : Type} [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {N q : ℕ} [NeZero N]

lemma finiteTrial_upper_fixedField_oai (M : Model (q+1)) (hM : Admissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) (h : Fin N → ℝ) :
    (∫ k,∫ z : Fin k → InteractionSample (q+1),
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (q+1) → Fin N)).expect
        (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*N))+
      (M.alpha:ℝ)*N*q*(∫ z,trialLog r (finiteTrialLaw r Q U x) m
        (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure) ≤
      ∑ s : Fin N,∫ k,∫ z : Fin k → InteractionSample (q+1),
        trialLog r (finiteTrialLaw r Q U x) m (siteLog z (h s))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*(q+1)) := by
  let m' : Fin (r+1) → ℝ := Fin.snoc m 1
  let m₀ : Fin (r+2) → ℝ := Fin.cons 0 m'
  have hpos : ∀ d,0 < m' d := snoc_exponents_pos hm
  have hend : m' (Fin.last r)=1 := Fin.snoc_last _ _
  have hend₀ : m₀ (Fin.last (r+1))=1 := by
    change Fin.cons (α := fun _ => ℝ) 0 m' (Fin.last r).succ=1
    simpa only [Fin.cons_succ] using hend
  let T : Fin N → KernelTower Spin (r+1) := fun _ => terminalTower false FiniteLaw.uniform r
  let V : Fin N → FinitePath Spin (r+1) → Spin := fun _ => terminalState r
  let f : Fin N → FinitePath Spin (r+1) → ℝ := fun s y => h s*spin (terminalState r y)
  let Up : R → KernelTower Λ (r+1) := fun b => pad a r (U b)
  let xp : R → FinitePath Λ (r+1) → ℝ := fun b y => x b (pathPrefix r y)
  have hx := upperPoissonCount_bound_firstMoment M hM (KernelTower.pi (r+1) T) Q Up
    (fun y s => V s (FinitePath.proj (r+1) y s)) xp m₀
    (cons_snoc_exponents_mono hm) (cons_snoc_exponents_nonneg hm)
    (fun d => hpos d) rfl hend₀ (Fin.last q)
    (fun y => ∑ s,f s (FinitePath.proj (r+1) y s)) (M.alpha*(q+1)*N)
  have hr : (M.alpha*(q+1)*N:ℝ≥0)/(q+1)=M.alpha*N := by
    have hp : (q+1:ℝ≥0)≠0 := by positivity
    field_simp
  have hs : (M.alpha*(q+1)*N:ℝ≥0)/N=M.alpha*(q+1) := by
    have hN : (N:ℝ≥0)≠0 := by exact_mod_cast NeZero.ne N
    exact mul_div_cancel_right₀ _ hN
  simp only [m₀,Fin.cons_succ,Nat.cast_add,Nat.cast_one] at hx
  change (∫ k,upperCountMean M (KernelTower.pi (r+1) T) Q Up
      (fun y s => V s (FinitePath.proj (r+1) y s)) xp m' (Fin.last q)
      (fun y => ∑ s,f s (FinitePath.proj (r+1) y s)) k 0 ∂poissonMeasure ((M.alpha*(q+1)*N)/(q+1)))+
      ((M.alpha*(q+1)*N:ℝ≥0):ℝ)*(((q+1-1:ℕ):ℝ)/(q+1))*
        (∫ z,edgeRoot Q Up xp m' z ∂M.disorder.toMeasure) ≤ _ at hx
  rw [hr,upperPoisson_cavity_separable M hM Q T Up V xp m' hpos (Fin.last q) f,hs] at hx
  dsimp only [T,V,f,Up,xp] at hx
  simp_rw [upperCountMean_real_terminal M hM Q r _ _ m' hpos hend,
    activeCountMean_site q M hM a r Q U x m' hpos hend,
    edgeRoot_pad r a Q U x m' (by rw [hend]; norm_num)] at hx
  have he : (fun d : Fin r => m' d.castSucc)=m := by funext d; exact Fin.snoc_castSucc _ _ d
  rw [he] at hx
  have hc : ((M.alpha*(q+1)*N:ℝ≥0):ℝ)*(((q+1-1:ℕ):ℝ)/(q+1))=(M.alpha:ℝ)*N*q := by
    simp only [Nat.add_sub_cancel,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    have hp : (q:ℝ)+1≠0 := by positivity
    field_simp
  rwa [hc] at hx

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField_oai := @OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField_oai
