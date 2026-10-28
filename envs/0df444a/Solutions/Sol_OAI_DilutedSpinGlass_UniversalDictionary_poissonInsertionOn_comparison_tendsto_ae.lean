-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:09:21.185926+00:00
-- url     : https://prove2.me/submissions/bd4a07f5-2c5a-4af2-92da-46b88f07b655

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physicalSubtree_limsup_tendsto

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
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonMoments
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

/-- A bounded measurable score belongs to every finite Lp space. -/
theorem bounded_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (p : ℝ≥0∞) : MemLp f p μ := by
  apply MemLp.of_bound hf.aestronglyMeasurable B
  exact ae_of_all _ (fun point => by simpa only [Real.norm_eq_abs] using hB point)

end DilutedSpinGlass

namespace DilutedSpinGlass

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Uniform bounds survive averaging a physical root coordinate. -/
theorem abs_integral_le_bound {f : Ω → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := f) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x))

end DilutedSpinGlass

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

theorem poisson_variance (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r)^2 ∂poissonMeasure r) = r := by
  have heq : (fun n : ℕ => ((n : ℝ)-r)^2) =
      (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*(n : ℝ) + (r : ℝ)^2) := by
    funext n
    ring
  rw [heq]
  have hi : Integrable (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*n) (poissonMeasure r) :=
    (poisson_integrable_count_sq r).sub ((poisson_integrable_count r).const_mul (2*(r : ℝ)))
  rw [integral_add hi (integrable_const ((r : ℝ)^2)),
    integral_sub (poisson_integrable_count_sq r) ((poisson_integrable_count r).const_mul (2*r)),
    integral_const_mul, poisson_second_moment, poisson_mean, integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

/-- Lipschitz sequences have a square-integrable Poisson law. -/
theorem poisson_memLp_lipschitz (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)|) :
    MemLp f 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr
  apply poisson_integrable_quadratic r (A := 2*(f 0)^2) (B := 2*C^2)
  intro n
  have h := hL n 0
  simp only [Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at h
  have hh : |f n| ≤ C*(n : ℝ)+|f 0| := by
    calc |f n| = |(f n-f 0)+f 0| := by rw [sub_add_cancel]
         _ ≤ |f n-f 0| + |f 0| := abs_add_le _ _
         _ ≤ C*(n : ℝ)+|f 0| := by linarith
  have hb : 0 ≤ C*(n : ℝ)+|f 0| := by positivity
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (f n), sq_abs (f 0),
    sq_nonneg (C*(n : ℝ)-|f 0|), mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hb (abs_nonneg (f n)))]

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- Adding one root coordinate gives the full Lipschitz bound in the count. -/
theorem nat_lipschitz_of_step {f : ℕ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ n, |f (n+1)-f n| ≤ C) : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)| := by
  have hle : ∀ n m, n ≤ m → |f m-f n| ≤ C*((m : ℝ)-(n : ℝ)) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have ha : |f (m+1)-f n| ≤ |f (m+1)-f m|+|f m-f n| := by
        calc
          |f (m+1)-f n| = |(f (m+1)-f m)+(f m-f n)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      push_cast
      nlinarith [h m]
  intro n m
  rcases le_total n m with hnm | hmn
  · rw [abs_sub_comm (f n), abs_sub_comm (n : ℝ), abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm : (n : ℝ) ≤ m))]
    exact hle n m hnm
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn : (m : ℝ) ≤ n))]
    exact hle m n hmn

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
-- module Solutions.OAIQ041_DS.DilutedSpin_ConvexBounds
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
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

 
theorem integral_abs_le_sqrt_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have hn := variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at hn
  simp only [Real.norm_eq_abs, Pi.pow_apply, sq_abs] at hn
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).mpr (by linarith)

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
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]

theorem abs_expect_le_expect_abs (P : FiniteLaw Ω) (f : Ω → ℝ) :
    |P.expect f| ≤ P.expect (fun x => |f x|) := by
  unfold expect
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro x _
    rw [abs_mul,abs_of_nonneg (P.nonneg x)])

end DilutedSpinGlass.FiniteLaw

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
namespace DilutedSpinGlass
open Filter Set
open scoped Topology BigOperators

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

section
open scoped BigOperators

namespace DilutedSpinGlass.Pattern

theorem sign_indicator (s t : Bool) : 1 + sign s * sign t = if s=t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [sign]

/-- Fourier inversion kernel on replica-spin patterns. -/
theorem character_kernel {ι : Type*} [Fintype ι] [DecidableEq ι] (e f : ι → Bool) :
    (∑ S : Finset ι, character S e * character S f) =
      if e=f then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  have hprod : (∑ S : Finset ι, character S e * character S f) =
      ∏ i : ι, (1 + sign (e i)*sign (f i)) := by
    rw [Finset.prod_one_add]
    simp only [character, ← Finset.prod_mul_distrib]
    apply Finset.sum_congr
    · ext S
      simp
    · intro S _
      rfl
  rw [hprod]
  simp_rw [sign_indicator]
  by_cases h : e=f
  · subst f
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ : ∃ i, e i ≠ f i := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Exact Walsh inversion for an arbitrary signed pattern mass. -/
theorem inversion {ι : Type*} [Fintype ι] [DecidableEq ι] (P : (ι → Bool) → ℝ) (e : ι → Bool) :
    P e = (∑ S : Finset ι, moment P S * character S e) / (2 : ℝ)^Fintype.card ι := by
  classical
  have hh : (∑ S : Finset ι, moment P S * character S e) =
      (2 : ℝ)^Fintype.card ι * P e := by
    simp only [moment, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, character_kernel]
    simp [mul_comm]
  rw [hh]
  have hne : (2 : ℝ)^Fintype.card ι ≠ 0 := by positivity
  field_simp

/-- The total variation discrepancy costs one per nonempty multioverlap.
Both masses have the same total, so the empty Fourier coefficient cancels. -/
theorem variation_le_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → Bool) → ℝ) (htotal : ∑ e, P e = ∑ e, Q e) :
    (∑ e, |P e-Q e|) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, |moment P S-moment Q S| := by
  classical
  let C := ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, |moment P S-moment Q S|
  have hzero : moment P ∅ - moment Q ∅ = 0 := by simpa [moment] using sub_eq_zero.mpr htotal
  have hpoint (e : ι → Bool) : |P e-Q e| ≤ C / (2 : ℝ)^Fintype.card ι := by
    rw [inversion P e, inversion Q e, ← sub_div, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ)^Fintype.card ι)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      |∑ S : Finset ι, (moment P S-moment Q S)*character S e| ≤
        ∑ S : Finset ι, |(moment P S-moment Q S)*character S e| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ S : Finset ι, |moment P S-moment Q S| := by simp [abs_mul]
      _ = C := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ∅), hzero]
        simp [C]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hne : (2 : ℝ)^Fintype.card ι ≠ 0 := by positivity
  have heq : (2 : ℝ)^Fintype.card ι * (C / (2 : ℝ)^Fintype.card ι) = C := by field_simp
  rw [heq] at h
  exact h

/-- Exact coordinatewise product telescoping, in a form usable for different
probability laws at different message labels. -/
theorem product_variation_step {α β : Type*} [Fintype α] [Fintype β]
    (P Q : α → ℝ) (U V : β → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hV : ∀ y, 0 ≤ V y)
    (hPt : ∑ x, P x = 1) (hVt : ∑ y, V y = 1) :
    (∑ x, ∑ y, |P x*U y-Q x*V y|) ≤
      (∑ x, |P x-Q x|) + ∑ y, |U y-V y| := by
  have hstep (x : α) (y : β) : |P x*U y-Q x*V y| ≤
      P x*|U y-V y| + |P x-Q x| *V y := by
    calc
      |P x*U y-Q x*V y| = |P x*(U y-V y)+(P x-Q x)*V y| := by ring_nf
      _ ≤ |P x*(U y-V y)| + |(P x-Q x)*V y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hP x), abs_of_nonneg (hV y)]
  calc
    _ ≤ ∑ x, ∑ y, (P x*|U y-V y| + |P x-Q x| *V y) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hstep x y))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hPt, hVt,
        mul_one, one_mul]
      ring

/-- Testing a spin pattern by a bounded observable costs twice the total variation. -/
theorem observable_variation {α : Type*} [Fintype α] (P Q f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x, P x*f x)-(∑ x, Q x*f x)| ≤ ∑ x, |P x-Q x| := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf x)))

end DilutedSpinGlass.Pattern

namespace DilutedSpinGlass.Pattern

/-- Tensorization with the sharp linear number of independent labels. -/
theorem product_variation {α : Type*} [Fintype α]
    (P Q : α → ℝ) (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hPt : ∑ x, P x = 1) (hQt : ∑ x, Q x = 1) (a : ℕ) :
    (∑ x : Fin a → α, |(∏ i, P (x i))-(∏ i, Q (x i))|) ≤
      (a : ℝ) * ∑ x, |P x-Q x| := by
  classical
  induction a with
  | zero => simp
  | succ a ih =>
    have heq : (∑ x : Fin (a+1) → α, |(∏ i, P (x i))-(∏ i, Q (x i))|) =
        ∑ x : α, ∑ y : Fin a → α, |P x*(∏ i, P (y i))-Q x*(∏ i, Q (y i))| := by
      rw [← (Fin.consEquiv (fun _ : Fin (a+1) => α)).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [heq]
    have htot : (∑ y : Fin a → α, ∏ i, Q (y i)) = 1 := by
      rw [← Fintype.prod_sum]
      simp only [hQt, Finset.prod_const_one]
    have hstep := product_variation_step P Q (fun y : Fin a → α => ∏ i, P (y i))
      (fun y : Fin a → α => ∏ i, Q (y i)) hP
      (fun y => Finset.prod_nonneg (fun i _ => hQ (y i))) hPt htot
    push_cast
    nlinarith

/-- The deterministic empirical-pattern comparison in comp:patterns.
The hypotheses are probability masses, and the conclusion involves ALL
nonempty replica-subset moments, with no assumption of decorrelation. -/
theorem pattern_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → Bool) → ℝ) (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hPt : ∑ x, P x = 1) (hQt : ∑ x, Q x = 1) (a : ℕ)
    (f : (Fin a → (ι → Bool)) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x, (∏ i, P (x i))*f x)-(∑ x, (∏ i, Q (x i))*f x)| ≤
      (a : ℝ) * ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, |moment P S-moment Q S| := by
  apply (observable_variation _ _ f hf).trans
  apply (product_variation P Q hP hQ hPt hQt a).trans
  exact mul_le_mul_of_nonneg_left (variation_le_moments P Q (hPt.trans hQt.symm)) (by positivity)

theorem empirical_nonneg {ι : Type*} [Fintype ι] {N : ℕ} (σ : Fin N → ι → Bool) (e : ι → Bool) :
    0 ≤ empirical σ e := by unfold empirical; positivity

/-- The normalization uses N>=1, as required for reservoir sizes. -/
theorem empirical_total {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} (hN : 0 < N)
    (σ : Fin N → ι → Bool) : (∑ e, empirical σ e) = 1 := by
  classical
  simp only [empirical, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have hne : (N : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self hne

 
theorem empirical_moment {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (σ : Fin N → ι → Bool) (S : Finset ι) :
    moment (empirical σ) S = (∑ i : Fin N, character S (σ i))/(N : ℝ) := by
  classical
  unfold moment empirical
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end DilutedSpinGlass.Pattern

open _root_.MeasureTheory

namespace DilutedSpinGlass.Pattern

variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem mass_le_one (P : α → ℝ) (hP : ∀ x, 0 ≤ P x) (hPt : ∑ x, P x = 1) (x : α) :
    P x ≤ 1 := by
  classical
  rw [← hPt]
  exact Finset.single_le_sum (fun i _ => hP i) (Finset.mem_univ x)

theorem mass_abs_average (P f : α → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hPt : ∑ x, P x = 1) (hf : ∀ x, |f x| ≤ 1) : |∑ x, P x*f x| ≤ 1 := by
  calc
    _ ≤ ∑ x, |P x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, P x := Finset.sum_le_sum (fun x _ => by
      rw [abs_mul, abs_of_nonneg (hP x)]
      exact mul_le_of_le_one_right (hP x) (hf x))
    _ = 1 := hPt

theorem bounded_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

end DilutedSpinGlass.Pattern

end

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology BigOperators

lemma limsup_finite_bound {ι : Type*} (s : Finset ι)
    (a : ℕ → ℝ) (f : ι → ℕ → ℝ) (c : ι → ℝ) (b : ℝ)
    (hc : ∀ i∈s, 0 ≤ c i) (ha : ∀ n, 0≤a n)
    (hf : ∀ i∈s, IsBoundedUnder (·≤·) atTop (f i))
    (h : ∀ n, a n≤b+∑ i∈s, c i*f i n) :
    limsup a atTop≤b+∑ i∈s, c i*limsup (f i) atTop := by
  classical
  have hcap (t : ℝ) (ht : 0<t) :
      limsup a atTop≤b+∑ i∈s, c i*(limsup (f i) atTop+t) := by
    have he : ∀ᶠ n in atTop, ∀ i∈s, f i n<limsup (f i) atTop+t := by
      apply (eventually_all_finite s.finite_toSet).mpr
      intro i hi
      exact eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht) (hf i hi)
    apply limsup_le_of_le
      (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha).frequently))
    filter_upwards [he] with n hn
    exact (h n).trans (add_le_add le_rfl (Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hn i hi).le (hc i hi))))
  have ht : Tendsto (fun t : ℝ => b+∑ i∈s, c i*(limsup (f i) atTop+t)) (𝓝[>] 0)
      (𝓝 (b+∑ i∈s, c i*limsup (f i) atTop)) := by
    have hh : ContinuousAt (fun t : ℝ => b+∑ i∈s, c i*(limsup (f i) atTop+t)) 0 := by fun_prop
    simpa using hh.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall hcap)

/-- Uniform summable remainders commute with the ordered limsup/grid limits.
No diagonal exchange of the two limits is used. -/
lemma series_double_limit (a : ℕ → ℕ → ℝ) (f : ℕ → ℕ → ℕ → ℝ)
    (c tail : ℕ → ℝ) (ha : ∀ L n, 0≤a L n)
    (hab : ∀ L, IsBoundedUnder (·≤·) atTop (a L))
    (hc : ∀ k, 0 ≤ c k) (hf : ∀ k L, IsBoundedUnder (·≤·) atTop (f k L))
    (hflim : ∀ k, Tendsto (fun L => limsup (f k L) atTop) atTop (𝓝 0))
    (htail : Tendsto tail atTop (𝓝 0))
    (h : ∀ K L n, a L n≤tail K+∑ k∈Finset.range K, c k*f k L n) :
    Tendsto (fun L => limsup (a L) atTop) atTop (𝓝 0) := by
  have ha0 (L : ℕ) : 0≤limsup (a L) atTop :=
    le_limsup_of_frequently_le ((Eventually.of_forall (ha L)).frequently) (hab L)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp (htail.eventually (Iio_mem_nhds (show 0<ε/2 by positivity)))
  have hb (L : ℕ) := limsup_finite_bound (Finset.range K) (a L) (fun k => f k L) c (tail K)
    (fun k _ => hc k) (ha L) (fun k _ => hf k L) (h K L)
  have hl : Tendsto (fun L => tail K+∑ k∈Finset.range K, c k*limsup (f k L) atTop)
      atTop (𝓝 (tail K)) := by
    simpa using tendsto_const_nhds.add (tendsto_finsetSum (Finset.range K)
      (fun k _ => (hflim k).const_mul (c k)))
  have hte : tail K<ε := (hK K le_rfl).trans (by linarith)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hl.eventually (Iio_mem_nhds hte))
  refine ⟨L, fun l hLl => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (ha0 l)]
  exact (hb l).trans_lt (hL l hLl)
end DilutedSpinGlass

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
namespace DilutedSpinGlass
open Filter
open scoped Topology BigOperators

lemma mixture_double_limit (f : ℕ → ℕ → ℕ → ℝ) (w B : ℕ → ℝ)
    (hw : ∀ k, 0≤w k) (hf : ∀ k L n, 0≤f k L n)
    (hB : ∀ k L n, f k L n≤B k)
    (hs : Summable (fun k => w k*B k))
    (hlim : ∀ k, Tendsto (fun L => limsup (f k L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (fun n => ∑' k, w k*f k L n) atTop) atTop (𝓝 0) := by
  have hi (L n : ℕ) : Summable (fun k => w k*f k L n) :=
    hs.of_nonneg_of_le (fun k => mul_nonneg (hw k) (hf k L n))
      (fun k => mul_le_mul_of_nonneg_left (hB k L n) (hw k))
  apply series_double_limit (fun L n => ∑' k, w k*f k L n) f w
    (fun K => ∑' k, w (k+K)*B (k+K))
  · intro L n; exact tsum_nonneg (fun k => mul_nonneg (hw k) (hf k L n))
  · intro L
    refine isBoundedUnder_of_eventually_le (a := ∑' k,w k*B k) (Eventually.of_forall (fun n => ?_))
    exact (hi L n).tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hB k L n) (hw k)) hs
  · exact hw
  · intro k L
    exact isBoundedUnder_of_eventually_le (a := B k) (Eventually.of_forall (hB k L))
  · exact hlim
  · exact tendsto_sum_nat_add (fun k => w k*B k)
  · intro K L n
    rw [← (hi L n).sum_add_tsum_nat_add K]
    have he : (∑' k,w (k+K)*f (k+K) L n) ≤ ∑' k,w (k+K)*B (k+K) :=
      ((hi L n).comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_left (hB (k+K) L n) (hw (k+K)))
        (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h))
    linarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DeviationLimitTools
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology

lemma limsup_affine_bound (a b : ℕ → ℝ) (c d : ℝ) (hc : 0 ≤ c)
    (ha : ∀ n, 0≤a n) (hb : IsBoundedUnder (·≤·) atTop b)
    (h : ∀ n, a n ≤ c*b n+d) : limsup a atTop ≤ c*limsup b atTop+d := by
  have he (ε : ℝ) (hε : 0<ε) : limsup a atTop ≤ c*(limsup b atTop+ε)+d := by
    apply limsup_le_of_le (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha).frequently))
    filter_upwards [eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε) hb] with n hn
    exact (h n).trans (add_le_add (mul_le_mul_of_nonneg_left hn.le hc) le_rfl)
  have ht : Tendsto (fun ε : ℝ => c*(limsup b atTop+ε)+d) (𝓝[>] 0)
      (𝓝 (c*limsup b atTop+d)) := by
    have hh : ContinuousAt (fun ε : ℝ => c*(limsup b atTop+ε)+d) 0 := by fun_prop
    simpa using hh.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall he)

lemma doubleLimit_young (a b : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0≤C)
    (ha : ∀ L n, 0≤a L n) (hb : ∀ L, IsBoundedUnder (·≤·) atTop (b L))
    (hbound : ∀ t, 0<t → ∀ L n, a L n≤C*(b L n/(2*t)+t/2))
    (hdecay : Tendsto (fun L => limsup (b L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (a L) atTop) atTop (𝓝 0) := by
  have hupper (t : ℝ) (ht : 0<t) (L : ℕ) :
      limsup (a L) atTop≤C*(limsup (b L) atTop/(2*t)+t/2) := by
    have hh := limsup_affine_bound (a L) (b L) (C/(2*t)) (C*t/2)
      (by positivity) (ha L) (hb L) (fun n => (hbound t ht L n).trans_eq (by ring))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hnonneg (L : ℕ) : 0≤limsup (a L) atTop := by
    obtain ⟨B,hB⟩ := hb L
    have hB' : ∀ᶠ n in atTop, b L n≤B := hB
    have ha' : IsBoundedUnder (·≤·) atTop (a L) := by
      apply isBoundedUnder_of_eventually_le (a := C*(B/2+1/2))
      filter_upwards [hB'] with n hn
      apply (hbound 1 (by norm_num) L n).trans
      apply mul_le_mul_of_nonneg_left _ hC
      norm_num
      linarith
    apply le_limsup_of_le ha'
    intro x hx
    obtain ⟨n,hn⟩ := hx.exists
    exact (ha L n).trans hn
  apply squeeze_triangle_grid_zero _ (C/2) hnonneg (by positivity)
    (fun t L => C*(limsup (b L) atTop/(2*t)+t/2)) _ (fun t ht L => hupper t ht L)
  intro t ht
  convert ((hdecay.div_const (2*t)).add_const (t/2)).const_mul C using 1
  all_goals try with_reducible_and_instances rfl
  simp
  ring

end DilutedSpinGlass

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

lemma injective (f : SplitMap T S) : Function.Injective f.leaf := by
  intro a b h
  apply (splitDepth_eq_height T a b).mp
  rw [← f.split,h,splitDepth_self]

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
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ}

theorem abs_spin (s : Spin) : |spin s| = 1 := by
  cases s <;> norm_num [spin]

end DilutedSpinGlass.PhysicalRoot
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
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

lemma clipReal_bound {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clipReal C x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

lemma clipReal_eq {C x : ℝ} (hx : |x| ≤ C) : clipReal C x = x := by
  simp only [clipReal,min_eq_right (abs_le.mp hx).2,max_eq_right (abs_le.mp hx).1]

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
-- module Solutions.OAIQ041_DS.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcreteReservoir
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology

lemma readSpin_eq {N : ℕ} (hN : 0 < N) (σ : Fin N → Spin) (i : Site N) :
    readSpin σ i = σ ⟨i.val,by have := i.isLt; simp only [max_eq_left (Nat.succ_le_iff.mpr hN)] at this; exact this⟩ := by
  unfold readSpin
  split_ifs with h
  · rfl
  · have := i.isLt
    simp only [max_eq_left (Nat.succ_le_iff.mpr hN)] at this
    exact (h this).elim

end DilutedSpinGlass.ConcreteReservoir
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

noncomputable local instance matrixEnergyPropDecidable_ra22664_1 (proposition : Prop) :
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

noncomputable local instance shapeMatrixPropDecidable_ra22664_1 (proposition : Prop) :
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

end DilutedSpinGlass.PrescribedTree
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

/-- Every proper child consumes strictly fewer leaves, without suppressing
or identifying distinct child occurrences with the same topology. -/
lemma child_leaf_card_lt (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (j : Fin k) : Fintype.card (C j).Leaf <
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  classical
  have hi : ∃ i : Fin k, i≠j := by
    by_cases hj : j=⟨0,k.property⟩
    · refine ⟨⟨1,by omega⟩,?_⟩
      intro h
      have hh := congrArg Fin.val (h.trans hj)
      change (1:ℕ)=0 at hh
      omega
    · exact ⟨⟨0,k.property⟩,Ne.symm hj⟩
  obtain ⟨i,hij⟩ := hi
  change _ < Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma,← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  apply Nat.lt_add_of_pos_right
  exact (leaf_card_pos (C i)).trans_le
    (Finset.single_le_sum (f := fun x : Fin k => Fintype.card (C x).Leaf) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩))

end DilutedSpinGlass.ReducedTopology
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

lemma gridExponents_last (L : ℕ) : gridExponents L (Fin.last L) = 1 := by
  simp only [gridExponents,Fin.val_last]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos L)))

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
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Poisson's add-one identity gives a *smoothing* estimate for every bounded
 test, without any regularity in the count. This is the needed large-rate
 transfer for the cavity reservoir, not the O(1) unmatched-points estimate. -/
lemma poisson_bounded_shift (r : ℝ≥0) (hr : 0 < r) {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ n, |f n|≤B) :
    |(∫ n, f (n+1) ∂poissonMeasure r)-(∫ n, f n ∂poissonMeasure r)| ≤
      B / Real.sqrt r := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  have hreal : (0:ℝ) < r := hr
  have hi : Integrable f (poissonMeasure r) := (bounded_memLp (Measurable.of_discrete) hf 1).integrable le_rfl
  have hi' : Integrable (fun n => f (n+1)) (poissonMeasure r) :=
    (bounded_memLp (Measurable.of_discrete) (fun n => hf (n+1)) 1).integrable le_rfl
  have hn : MemLp (fun n : ℕ => (n:ℝ)) 2 (poissonMeasure r) :=
    poisson_memLp_lipschitz r (by norm_num : (0:ℝ)≤1) (fun _ _ => by simp)
  have hc := hn.sub (memLp_const (r:ℝ))
  have hcs : (∫ n : ℕ, |(n:ℝ)-r| ∂poissonMeasure r)≤Real.sqrt r := by
    simpa only [Pi.sub_apply,poisson_variance] using integral_abs_le_sqrt_sq (poissonMeasure r) hc
  have hnf : Integrable (fun n : ℕ => (n:ℝ)*f n) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 0) (B := B)
    intro n
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
    simpa only [zero_add,mul_comm] using mul_le_mul_of_nonneg_left (hf n) (Nat.cast_nonneg n)
  have hid : Integrable (fun n : ℕ => ((n:ℝ)-r)*f n) (poissonMeasure r) := by
    have heq : (fun n : ℕ => ((n:ℝ)-r)*f n)=
        (fun n : ℕ => (n:ℝ)*f n)-(fun n => (r:ℝ)*f n) := by
      funext n
      change ((n:ℝ)-r)*f n=(n:ℝ)*f n-(r:ℝ)*f n
      ring
    rw [heq]
    exact hnf.sub (hi.const_mul r)
  have he : (r:ℝ)*((∫ n, f (n+1) ∂poissonMeasure r)-(∫ n, f n ∂poissonMeasure r)) =
      ∫ n : ℕ, ((n:ℝ)-r)*f n ∂poissonMeasure r := by
    simp_rw [sub_mul]
    rw [integral_sub hnf (hi.const_mul r),integral_const_mul,poisson_add_one r f hi',mul_sub]
  have hab := abs_integral_le_integral_abs (f := fun n : ℕ => ((n:ℝ)-r)*f n) (μ := poissonMeasure r)
  have hm : (∫ n : ℕ, |((n:ℝ)-r)*f n| ∂poissonMeasure r) ≤
      B * Real.sqrt r := by
    calc
      _ ≤ ∫ n : ℕ, |(n:ℝ)-r| * B ∂poissonMeasure r := by
        apply integral_mono hid.abs ((hc.integrable (by norm_num)).abs.mul_const B)
        intro n
        change |((n:ℝ)-r)*f n| ≤ |(n:ℝ)-r| * B
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hf n) (abs_nonneg _)
      _ = B*(∫ n : ℕ, |(n:ℝ)-r| ∂poissonMeasure r) := by rw [integral_mul_const,mul_comm]
      _ ≤ B*Real.sqrt r := mul_le_mul_of_nonneg_left hcs hB
  rw [← he,abs_mul,abs_of_pos hreal] at hab
  have hs : 0<Real.sqrt (r:ℝ) := Real.sqrt_pos.2 hreal
  have hsq := Real.sq_sqrt (le_of_lt hreal)
  rw [le_div_iff₀ hs]
  nlinarith [hab.trans hm]

lemma poisson_bounded_rate_add (r s : ℝ≥0) (hr : 0 < r) {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ n, |f n|≤B) :
    |(∫ n, f n ∂poissonMeasure (r+s))-(∫ n, f n ∂poissonMeasure r)| ≤
      B*(s:ℝ)/Real.sqrt r := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  let g (k : ℕ) := ∫ n, f (n+k) ∂poissonMeasure r
  have hg (k : ℕ) : |g (k+1)-g k|≤B/Real.sqrt r := by
    simpa only [g,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      poisson_bounded_shift r hr (f := fun n => f (n+k)) (fun n => hf (n+k))
  have hl := nat_lipschitz_of_step (div_nonneg hB (Real.sqrt_nonneg r)) hg
  have hgi : Integrable g (poissonMeasure s) :=
    (bounded_memLp (Measurable.of_discrete) (fun k => abs_integral_le_bound (μ := poissonMeasure r) (fun n => hf (n+k))) 1).integrable le_rfl
  have hc : |(∫ k, g k ∂poissonMeasure s)-g 0| ≤ B/Real.sqrt r*(s:ℝ) := by
    have hconst : (∫ _ : ℕ, g 0 ∂poissonMeasure s)=g 0 := by simp
    rw [← hconst,← integral_sub hgi (integrable_const (g 0))]
    calc
      _ ≤ ∫ k, |g k-g 0| ∂poissonMeasure s := abs_integral_le_integral_abs
      _ ≤ ∫ k : ℕ, (B/Real.sqrt r)*(k:ℝ) ∂poissonMeasure s := by
        apply integral_mono (hgi.sub (integrable_const (g 0))).abs ((poisson_integrable_count s).const_mul _)
        intro k
        change |g k-g 0|≤(B/Real.sqrt r)*(k:ℝ)
        simpa only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k)] using hl k 0
      _ = _ := by rw [integral_const_mul,poisson_mean]
  have hi (t : ℝ≥0) : Integrable f (poissonMeasure t) :=
    (bounded_memLp (Measurable.of_discrete) hf 1).integrable le_rfl
  have hconv : (∫ k, g k ∂poissonMeasure s)=∫ n, f n ∂poissonMeasure (r+s) := by
    rw [add_comm r s,← poissonMeasure_conv_poissonMeasure s r]
    rw [integral_conv (by simpa only [poissonMeasure_conv_poissonMeasure] using hi (s+r))]
    simp only [g,Nat.add_comm]
  dsimp only [g] at hc
  simp only [Nat.add_zero] at hc
  change |(∫ k, g k ∂poissonMeasure s)-(∫ n, f n ∂poissonMeasure r)|≤_ at hc
  rw [hconv] at hc
  simpa only [div_mul_eq_mul_div] using hc
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeEstimates
attribute [-instance] _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

lemma BoundedDistance.prod {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (h : BoundedDistance μ ν d)
    (τ : Measure Y) [IsProbabilityMeasure τ] :
    BoundedDistance (μ.prod τ) (ν.prod τ) d := by
  intro f hm B hf
  have hi (κ : Measure X) [IsProbabilityMeasure κ] : Integrable f (κ.prod τ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_prod _ (hi μ),integral_prod _ (hi ν)]
  exact h _ hm.stronglyMeasurable.integral_prod_right'.measurable B
    (fun x => abs_integral_le_bound (fun y => hf (x,y)))

lemma BoundedDistance.prod_left {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (h : BoundedDistance μ ν d)
    (τ : Measure Y) [IsProbabilityMeasure τ] :
    BoundedDistance (τ.prod μ) (τ.prod ν) d := by
  intro f hm B hf
  have hi (κ : Measure X) [IsProbabilityMeasure κ] : Integrable f (τ.prod κ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_prod_symm _ (hi μ),integral_prod_symm _ (hi ν)]
  exact h _ hm.stronglyMeasurable.integral_prod_left'.measurable B
    (fun x => abs_integral_le_bound (fun y => hf (y,x)))

lemma poisson_boundedDistance (r s : ℝ≥0) (hr : 0 < r) :
    BoundedDistance (ProbabilityTheory.poissonMeasure (r+s))
      (ProbabilityTheory.poissonMeasure r) ((s:ℝ)/Real.sqrt r) := by
  intro f _ B hf
  simpa only [mul_div_assoc] using poisson_bounded_rate_add r s hr hf

lemma BoundedDistance.familyLaw {I : Type} [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {Z : I → Type} [∀ i, MeasurableSpace (Z i)]
    {μ ν : Measure I} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℝ} (h : BoundedDistance μ ν d)
    (κ : (i : I) → Measure (Z i)) [∀ i, IsProbabilityMeasure (κ i)] :
    BoundedDistance (familyLaw μ κ) (familyLaw ν κ) d := by
  intro f hm B hf
  have hi (ρ : Measure I) [IsProbabilityMeasure ρ] : Integrable f (DilutedSpinGlass.familyLaw ρ κ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_familyLaw μ κ (fun i x => f ⟨i,x⟩)
      (fun i => hm.comp (measurable_sigmaMk i)) (hi μ),
    integral_familyLaw ν κ (fun i x => f ⟨i,x⟩)
      (fun i => hm.comp (measurable_sigmaMk i)) (hi ν)]
  exact h _ (measurable_of_countable _) B
    (fun i => abs_integral_le_bound (fun x => hf ⟨i,x⟩))

lemma fullRoot_boundedDistance {M : ℕ} {I : Type} [MeasurableSpace I]
    (ξ : Fin M → Measure Y) [∀ i, IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s t : ℝ≥0) (hr : 0 < r) :
    BoundedDistance (fullRootLaw ξ μ ν (r+s) t) (fullRootLaw ξ μ ν r t)
      ((s:ℝ)/Real.sqrt r) := by
  exact (((poisson_boundedDistance r s hr).familyLaw
    (fun k => rootLaw k (fun _ => μ))).prod (compoundRootLaw ν t)).prod_left (rootLaw M ξ)

end DilutedSpinGlass

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

noncomputable local instance fullRegularSelectionDecidableEq_ra22664_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

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
-- module Solutions.OAIQ041_DS.DilutedSpin_MixedDeviation
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z]

lemma mixedDeviation_nonneg (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ) :
    0 ≤ mixedDeviation μ Ω P F := integral_nonneg (fun z => (P z).expect_nonneg (fun _ => abs_nonneg _))

lemma expect_centered_sq (Ω : Type) [Fintype Ω] (P : FiniteLaw Ω) (F : Ω → ℝ) (c : ℝ) :
    P.expect (fun w => (F w-c)^2)=P.expect (fun w => (F w)^2)-2*c*P.expect F+c^2 := by
  calc
    _ = P.expect (fun w => (F w)^2-(2*c)*F w+c^2) := P.expect_congr (fun w => by ring)
    _ = _ := by simp only [expect_add,expect_sub,expect_mul_left,expect_const]

lemma mixedDeviation_le_variance (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ)
    (habs : Integrable (fun z => (P z).expect (fun w => |F z w-(∫ y, (P y).expect (F y) ∂μ)|)) μ)
    {t : ℝ} (ht : 0<t) :
    mixedDeviation μ Ω P F ≤ mixedVariance μ Ω P F/(2*t)+t/2 := by
  let c := ∫ y, (P y).expect (F y) ∂μ
  have hi : Integrable (fun z => (P z).expect (fun w => (F z w-c)^2)) μ := by
    simp_rw [expect_centered_sq]
    exact (hFsq.sub (hF.const_mul (2*c))).add (integrable_const (c^2))
  rw [mixedVariance_eq_centered μ Ω P F hF hFsq]
  unfold mixedDeviation
  calc
    _ ≤ ∫ z, (P z).expect (fun w => (F z w-c)^2)/(2*t)+t/2 ∂μ := by
      apply integral_mono habs ((hi.div_const (2*t)).add (integrable_const (t/2)))
      intro z
      change (P z).expect (fun w => |F z w-c|) ≤ (P z).expect (fun w => (F z w-c)^2)/(2*t)+t/2
      rw [← expect_div,← expect_const (P z) (t/2),← expect_add]
      apply expect_mono
      intro w
      have hs := sq_nonneg (|F z w-c|-t)
      have ha := sq_abs (F z w-c)
      apply (mul_le_mul_iff_left₀ (by positivity : 0<2*t)).mp
      calc
        |F z w-c| * (2*t) ≤ (F z w-c)^2+t^2 := by nlinarith
        _ = ((F z w-c)^2/(2*t)+t/2)*(2*t) := by field_simp
    _ = _ := by rw [integral_add (hi.div_const (2*t)) (integrable_const (t/2)),integral_div,integral_const]; simp only [probReal_univ,one_smul]; rfl

end DilutedSpinGlass.FiniteLaw

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

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
variable {Z : Type} [MeasurableSpace Z]

lemma mixedDeviation_distance {μ ν : Measure Z} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (hd : BoundedDistance μ ν d)
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (P : (z : Z) → FiniteLaw (Ω z))
    (F : (z : Z) → Ω z → ℝ) (hF : ∀ z w, |F z w|≤1)
    (hm : Measurable (fun z => (P z).expect (F z)))
    (ha : ∀ c : ℝ, Measurable (fun z => (P z).expect (fun w => |F z w-c|))) :
    |mixedDeviation μ Ω P F-mixedDeviation ν Ω P F|≤3*d := by
  let c := ∫ z, (P z).expect (F z) ∂μ
  let e := ∫ z, (P z).expect (F z) ∂ν
  let G (a : ℝ) (z : Z) := (P z).expect (fun w => |F z w-a|)
  have hc : |c|≤1 := abs_integral_le_bound (fun z => (P z).abs_expect_le (hF z))
  have he : |e|≤1 := abs_integral_le_bound (fun z => (P z).abs_expect_le (hF z))
  have hce : |c-e|≤d := by simpa only [one_mul] using hd _ hm 1 (fun z => (P z).abs_expect_le (hF z))
  have hG (a : ℝ) (z : Z) : |G a z|≤1+|a| := by
    apply (P z).abs_expect_le
    intro w
    rw [abs_abs]
    exact (abs_sub (F z w) a).trans (by linarith [hF z w])
  have hi (a : ℝ) (κ : Measure Z) [IsProbabilityMeasure κ] : Integrable (G a) κ :=
    (bounded_memLp (ha a) (hG a) 1).integrable le_rfl
  have hGc (z : Z) : |G c z|≤2 := (hG c z).trans (by linarith)
  have hdist : |(∫ z, G c z ∂μ)-(∫ z, G c z ∂ν)|≤2*d := hd _ (ha c) 2 hGc
  have hchange : |(∫ z, G c z ∂ν)-(∫ z, G e z ∂ν)|≤|c-e| := by
    rw [← integral_sub (hi c ν) (hi e ν)]
    apply abs_integral_le_bound
    intro z
    change |(P z).expect (fun w => |F z w-c|)-(P z).expect (fun w => |F z w-e|)|≤_
    rw [← expect_sub]
    apply (P z).abs_expect_le
    intro w
    calc
      _ ≤ |(F z w-c)-(F z w-e)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |c-e| := by rw [show (F z w-c)-(F z w-e)=e-c by ring,abs_sub_comm]
  change |(∫ z, G c z ∂μ)-(∫ z, G e z ∂ν)|≤_
  have ht := (abs_sub_le (∫ z, G c z ∂μ) (∫ z, G c z ∂ν) (∫ z, G e z ∂ν)).trans
    (add_le_add hdist (hchange.trans hce))
  linarith

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HierarchyBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.hierarchyBasicDecidableEq
lemma mem_nodes (k : ℕ+) (hk : 2≤(k:ℕ)) (s : Finset ReducedTopology)
    (C : Fin k → ReducedTopology) (hC : ∀ j, C j∈s) : .node k hk C∈nodes k hk s := by
  exact Finset.mem_image.mpr ⟨fun j => ⟨C j,hC j⟩,Finset.mem_univ _,rfl⟩

lemma node_arity_le_leaf_card (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) :
    (k:ℕ)≤Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change _≤Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  have := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ => Nat.succ_le_iff.mpr (leaf_card_pos (C j)))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.succ_eq_add_one,zero_add,mul_one] using this

lemma mem_boundedTopologies (n : ℕ) (S : ReducedTopology)
    (h : Fintype.card S.Leaf≤n) : S∈boundedTopologies n := by
  induction n generalizing S with
  | zero => have := leaf_card_pos S; omega
  | succ n ih =>
    cases S with
    | leaf => exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    | node k hk C =>
      apply Finset.mem_union_right
      have hk' := (node_arity_le_leaf_card k hk C).trans h
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨k,by omega⟩,Finset.mem_univ _,?_⟩
      simp only [dite_true,hk]
      apply mem_nodes
      intro j
      apply ih
      have := child_leaf_card_lt k hk C j
      omega

end DilutedSpinGlass.ReducedTopology

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

noncomputable local instance qTreeLawDecidableEq_ra22664_1 (type : Type) :
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

lemma qExpect_mul_const {n : ℕ} (m : Fin (n+1) → ℝ)
    (F : PrescribedTree n → ℝ) (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T*c) k S=qExpect m F k S*c := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,Finset.sum_mul,mul_assoc]

/-- Only the genuine reachable terminal leaf number is required. -/
lemma qExpect_mono_leaves {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n)
    (hFG : ∀ T, T.leaves=S.leaves+k → F T≤G T) :
    qExpect m F k S≤qExpect m G k S := by
  induction k generalizing S with
  | zero => exact hFG S (by omega)
  | succ k ih =>
    apply Finset.sum_le_sum
    intro v _
    apply mul_le_mul_of_nonneg_left
    · apply ih
      intro T hT
      apply hFG
      rw [leaves_grow] at hT
      omega
    · exact div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)

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

section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

noncomputable local instance finiteLogExpansionDecidableEq_ra22664_1 (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
/-- Suppression of unary vertices loses neither the leveled tree nor labels. -/
theorem exists_realize {r : ℕ} (T : PrescribedTree r) (d : ℕ) :
    ∃ (S : ReducedTopology) (q : S.Vertex → ℕ),
      Admissible S q d (d+r) ∧ realize r d S q=T := by
  induction T generalizing d with
  | leaf => exact ⟨.leaf,Empty.elim,trivial,rfl⟩
  | @node r k C ih =>
    classical
    by_cases hk : (k:ℕ)=1
    · have hk' : k=1 := Subtype.ext hk
      subst k
      obtain ⟨S,q,hq,he⟩ := ih 0 (d+1)
      refine ⟨S,q,?_,?_⟩
      · exact admissible_mono_lower S q (lo := d+1) (Nat.le_succ d) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq)
      · rw [realize_unary_of_later]
        · rw [he]
          unfold PrescribedTree.unary
          congr 1
          funext i
          have hi : i=0 := Fin.ext (by have h := i.isLt; change i.val<1 at h; simp only [Fin.val_zero]; omega)
          rw [hi]
        · intro v
          have := admissible_lower S q hq v
          omega
    · have hk2 : 2≤(k:ℕ) := by have := k.pos; omega
      choose S q hq he using fun i => ih i (d+1)
      let Q : (ReducedTopology.node k hk2 S).Vertex → ℕ :=
        fun v => match v with | none => d | some ⟨i,w⟩ => q i w
      refine ⟨.node k hk2 S,Q,?_,?_⟩
      · refine ⟨le_rfl,by change d<d+(r+1); omega,?_⟩
        intro i
        simpa only [Q,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq i
      · simp only [realize,Q,lt_self_iff_false,ite_false]
        congr 1
        funext i
        exact he i

/-- For bounded leaf number there are finitely many possible reduced shapes. -/
theorem exists_bounded_realize {r : ℕ} (T : PrescribedTree r) (K : ℕ)
    (hK : T.leaves≤K) :
    ∃ (S : ReducedTopology), S∈boundedTopologies K ∧
      ∃ q : S.Vertex → Fin r,
        Admissible S (fun v => q v) 0 r ∧ realize r 0 S (fun v => q v)=T := by
  obtain ⟨S,q,ha,he⟩ := exists_realize T 0
  have hc : Fintype.card S.Leaf≤K := by
    rw [← realize_leaves r 0 S q ha,he]
    exact hK
  refine ⟨S,mem_boundedTopologies K S hc,fun v => ⟨q v,?_⟩,by simpa using ha,he⟩
  simpa using admissible_upper S q ha v

end DilutedSpinGlass.ReducedTopology

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
namespace DilutedSpinGlass
open scoped BigOperators

lemma insertionRadius_pos {C : ℝ} (hC : 0≤C) : 0 < insertionRadius C := by
  have he : Real.exp (-2*C-1)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  dsimp only [insertionRadius]
  linarith

lemma insertionRadius_lt_one (C : ℝ) : insertionRadius C < 1 := by
  have := Real.exp_pos (-2*C-1)
  dsimp only [insertionRadius]
  linarith

lemma normalizedInsertion_bound {C x : ℝ} (hC : 0≤C) (hx : |x|≤C) :
    |normalizedInsertion C x|≤1 := by
  have hc := insertionRadius_pos hC
  have helo : Real.exp (-2*C-1)≤Real.exp (x-C) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).1])
  have hehi : Real.exp (x-C)≤1 := Real.exp_le_one_iff.mpr (by linarith [(abs_le.mp hx).2])
  rw [normalizedInsertion,abs_div,abs_of_pos hc,div_le_one₀ hc]
  apply abs_le.mpr
  dsimp only [insertionRadius]
  constructor <;> linarith

lemma normalizedInsertion_log {C x : ℝ} (hC : 0≤C) :
    Real.log (1+insertionRadius C*normalizedInsertion C x)=x-C := by
  have hc := ne_of_gt (insertionRadius_pos hC)
  rw [normalizedInsertion,mul_div_cancel₀ _ hc]
  convert Real.log_exp (x-C) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

namespace KernelTower
variable {Ω : Type} [Fintype Ω]
lemma backwardLog_normalized {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ i : Fin n, m i.succ≠0)
    (F : FinitePath Ω n → ℝ) {C : ℝ} (hC : 0≤C) :
    backwardLog n T (fun i => m i.succ) F =
      PrescribedTree.logInsertion T m (fun y => normalizedInsertion C (F y)) (insertionRadius C)+C := by
  unfold PrescribedTree.logInsertion
  simp_rw [normalizedInsertion_log hC]
  rw [← backwardLog_add n T _ hm (fun y => F y-C) C]
  congr 1
  funext y
  ring
end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SubsetTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

namespace SplitMap
variable {n : ℕ} {k l : ℕ+} {C : Fin k → PrescribedTree n} {D : Fin l → PrescribedTree n}

lemma leaves_le {n : ℕ} {S T : PrescribedTree n} (f : SplitMap S T) : S.leaves ≤ T.leaves := by
  simpa only [card_leaf] using Fintype.card_le_of_injective f.leaf f.injective

end SplitMap

/-- Every nonempty set of leaf positions has its literal induced leveled tree.
Singleton unary stretches are kept; a SplitMap retains the exact pair splits. -/
theorem exists_subset_tree {n : ℕ} (T : PrescribedTree n) (A : Finset T.Leaf) (hA : A.Nonempty) :
    ∃ (U : PrescribedTree n) (f : SplitMap U T), ∀ b, (∃ a, f.leaf a=b) ↔ b∈A := by
  classical
  induction T with
  | leaf =>
    refine ⟨.leaf,⟨id,fun _ _ => rfl⟩,?_⟩
    intro b
    have hb : b∈A := by obtain ⟨a,ha⟩ := hA; cases a; cases b; exact ha
    exact iff_of_true ⟨b,rfl⟩ hb
  | @node n k C ih =>
    let B (i : Fin k) : Finset (C i).Leaf := Finset.univ.filter (fun b => (⟨i,b⟩ : (PrescribedTree.node k C).Leaf)∈A)
    let I := {i : Fin k // (B i).Nonempty}
    have hn : Nonempty I := by
      obtain ⟨⟨i,b⟩,hb⟩ := hA
      refine ⟨⟨i,⟨b,?_⟩⟩⟩
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hb
    let : Nonempty I := hn
    let l : ℕ+ := ⟨Fintype.card I,Fintype.card_pos⟩
    let e : Fin l ≃ I := (Fintype.equivFin I).symm
    choose U f hf using fun i : I => ih i.val (B i.val) i.property
    let g : SplitMap (.node l (fun j => U (e j))) (.node k C) :=
      SplitMap.ofChildren (fun j => (e j).val)
        (fun i j h => e.injective (Subtype.ext h)) (fun j => f (e j))
    refine ⟨.node l (fun j => U (e j)),g,?_⟩
    rintro ⟨i,b⟩
    constructor
    · rintro ⟨⟨j,a⟩,ha⟩
      have hh : (⟨(e j).val,(f (e j)).leaf a⟩ : (PrescribedTree.node k C).Leaf)∈A := by
        exact (Finset.mem_filter.mp ((hf (e j) _).mp ⟨a,rfl⟩)).2
      exact ha ▸ hh
    · intro hb
      have hbi : b∈B i := by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb
      let t : I := ⟨i,⟨b,hbi⟩⟩
      obtain ⟨a,ha⟩ := (hf t b).mpr hbi
      have hh : ∃ a' : (U (e (e.symm t))).Leaf,
          (⟨(e (e.symm t)).val,(f (e (e.symm t))).leaf a'⟩ : (PrescribedTree.node k C).Leaf)=⟨i,b⟩ := by
        rw [Equiv.apply_symm_apply]
        exact ⟨a,congrArg (fun z : (C i).Leaf => (⟨i,z⟩ : (PrescribedTree.node k C).Leaf)) ha⟩
      obtain ⟨a',ha'⟩ := hh
      exact ⟨⟨e.symm t,a'⟩,ha'⟩

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

namespace DilutedSpinGlass


/-- Uniform bounds on a finite probability-weighted exponential sum. -/
theorem weighted_exp_bounds {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    Real.exp (-B) ≤ ∑ i, w i * Real.exp (f i) ∧
      (∑ i, w i * Real.exp (f i)) ≤ Real.exp B := by
  have hlo : ∀ i, Real.exp (-B) ≤ Real.exp (f i) :=
    fun i => Real.exp_le_exp.mpr (abs_le.mp (hf i)).1
  have hhi : ∀ i, Real.exp (f i) ≤ Real.exp B :=
    fun i => Real.exp_le_exp.mpr (abs_le.mp (hf i)).2
  constructor
  · calc
      Real.exp (-B) = ∑ i, w i * Real.exp (-B) := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlo i) (hw i))
  · calc
      _ ≤ ∑ i, w i * Real.exp B :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hhi i) (hw i))
      _ = Real.exp B := by rw [← Finset.sum_mul, hs, one_mul]

theorem weighted_log_exp_bound {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    |Real.log (∑ i, w i * Real.exp (f i))| ≤ B := by
  obtain ⟨hlo, hhi⟩ := weighted_exp_bounds w f hw hs hf
  have hp := (Real.exp_pos _).trans_le hlo
  exact abs_le.mpr ⟨(Real.le_log_iff_exp_le hp).mpr hlo,
    (Real.log_le_iff_le_exp hp).mpr hhi⟩

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasureHierarchy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

namespace DilutedSpinGlass.MeasureMean

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bounded_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem exp_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) (m : ℝ) : Integrable (fun x => Real.exp (m*f x)) μ := by
  apply bounded_integrable μ (hf.const_mul m).exp
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc m*f x ≤ |m*f x| := le_abs_self _
       _ = |m| * |f x| := abs_mul _ _
       _ ≤ |m| * B := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem exp_integral_pos {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) (m : ℝ) : 0 < ∫ x, Real.exp (m*f x) ∂μ :=
  integral_exp_pos (exp_integrable μ hf hb m)

theorem logMean_const {m : ℝ} (hm : m ≠ 0) (a : ℝ) :
    logMean μ m (fun _ => a) = a := by
  simp [logMean, Real.log_exp, hm]

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ C) (hfg : ∀ x, f x ≤ g x) :
    logMean μ m f ≤ logMean μ m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (exp_integral_pos μ hf hfb m)
  exact integral_mono (exp_integrable μ hf hfb m) (exp_integrable μ hg hgb m)
    (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg x) hm.le))

theorem logMean_add_const {m : ℝ} (hm : m ≠ 0) {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) (a : ℝ) :
    logMean μ m (fun x => f x+a) = logMean μ m f+a := by
  unfold logMean
  simp_rw [mul_add, Real.exp_add]
  rw [integral_mul_const, Real.log_mul (ne_of_gt (exp_integral_pos μ hf hb m))
    (Real.exp_ne_zero _), Real.log_exp]
  field_simp

theorem logMean_stability {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} {B C D : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ C) (hfg : ∀ x, |f x-g x| ≤ D) :
    |logMean μ m f-logMean μ m g| ≤ D := by
  have haddb (g : Ω → ℝ) (C : ℝ) (hg : ∀ x, |g x| ≤ C) (x : Ω) :
      |g x+D| ≤ C+|D| := (abs_add_le _ _).trans (add_le_add (hg x) le_rfl)
  have h1 := logMean_mono μ hm hf (hg.add_const D) hfb (haddb g C hgb)
    (fun x => by have := (abs_le.mp (hfg x)).2; linarith)
  have h2 := logMean_mono μ hm hg (hf.add_const D) hgb (haddb f B hfb)
    (fun x => by have := (abs_le.mp (hfg x)).1; linarith)
  rw [logMean_add_const μ hm.ne' hg hgb] at h1
  rw [logMean_add_const μ hm.ne' hf hfb] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem logMean_bound {m : ℝ} (hm : 0 < m) {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) : |logMean μ m f| ≤ B := by
  have h := logMean_stability μ hm hf measurable_const hb
    (fun _ => (by simp : |(0 : ℝ)| ≤ 0)) (by simpa using hb)
  simpa only [logMean_const μ hm.ne', sub_zero] using h

end DilutedSpinGlass.MeasureMean

namespace DilutedSpinGlass
attribute [local instance] OAI.DilutedSpinGlass.measureHierarchyContinuousMeasurableSpace
local instance measureHierarchyContinuousBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_continuous_bound {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) :
    Continuous (logMean r g m) ∧ ∀ eta, |logMean r g m eta| ≤ B := by
  induction r with
  | zero => exact ⟨hg, hB⟩
  | succ r ih =>
    obtain ⟨hc, hb⟩ := ih (fun i => m i.succ) (fun i => hm i.succ)
    let f := logMean r g (fun i => m i.succ)
    let F : (ι → Hierarchy r) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => Real.exp (m 0 * f x)) (Real.continuous_exp.comp (hc.const_mul (m 0)))
      (Real.exp (|m 0| * B)) (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hb x))
    have hpos (eta : ι → Hierarchy (r+1)) : 0 < ∫ x, F x ∂(ProbabilityMeasure.pi eta) :=
      MeasureMean.exp_integral_pos (ProbabilityMeasure.pi eta).toMeasure hc.measurable hb (m 0)
    have hcont : Continuous (fun eta : ι → Hierarchy (r+1) => ∫ x, F x ∂(ProbabilityMeasure.pi eta)) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp
        ProbabilityMeasure.continuous_pi
    refine ⟨(hcont.log (fun eta => (hpos eta).ne')).div_const (m 0), ?_⟩
    intro eta
    exact MeasureMean.logMean_bound (ProbabilityMeasure.pi eta).toMeasure (hm 0) hc.measurable hb

 theorem trialLog_continuous_bound {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) :
    Continuous (fun ζ => trialLog r ζ m g) ∧ ∀ ζ, |trialLog r ζ m g| ≤ B := by
  obtain ⟨hc,hb⟩ := logMean_continuous_bound r g hg hB m hm
  let F : (ι → Hierarchy r) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (logMean r g m) hc B (fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hpi : Continuous (fun ζ : Hierarchy (r+1) => ProbabilityMeasure.pi (fun _ : ι => ζ)) :=
    ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ => continuous_id))
  refine ⟨(ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp hpi, ?_⟩
  intro ζ
  change |∫ x, F x ∂(ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure| ≤ B
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure)
      (ae_of_all _ (fun x => (show ‖F x‖ ≤ B from by simpa [F] using hb x))))

end DilutedSpinGlass

namespace DilutedSpinGlass
attribute [local instance] OAI.DilutedSpinGlass.measureHierarchyStabilityMeasurableSpace
local instance measureHierarchyStabilityBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (eta : ι → Hierarchy r) :
    |logMean r f m eta-logMean r g m eta| ≤ D := by
  induction r with
  | zero => exact hD eta
  | succ r ih =>
    obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB (fun i => m i.succ) (fun i => hm i.succ)
    obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC (fun i => m i.succ) (fun i => hm i.succ)
    exact MeasureMean.logMean_stability (ProbabilityMeasure.pi eta).toMeasure (hm 0)
      hfc.measurable hgc.measurable hfb hgb (ih (fun i => m i.succ) (fun i => hm i.succ))

theorem trialLog_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m f-trialLog r ζ m g| ≤ D := by
  obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB m hm
  obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC m hm
  let μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure
  have hiF : Integrable (logMean r f m) μ := MeasureMean.bounded_integrable μ hfc.measurable hfb
  have hiG : Integrable (logMean r g m) μ := MeasureMean.bounded_integrable μ hgc.measurable hgb
  change |(∫ eta, logMean r f m eta ∂μ)-(∫ eta, logMean r g m eta ∂μ)| ≤ D
  rw [← integral_sub hiF hiG]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (fun eta =>
      (show ‖logMean r f m eta - logMean r g m eta‖ ≤ D from by
        simpa only [Real.norm_eq_abs] using logMean_stability r f g hf hg hB hC hD m hm eta)))

 theorem continuous_q (s : Spin) : Continuous (fun x => q x s) := by
  unfold q
  apply (Real.continuous_exp.comp (continuous_id.mul continuous_const)).div
    (continuous_const.mul Real.continuous_cosh)
  intro x
  exact mul_ne_zero (by norm_num) (Real.cosh_pos x).ne'

end DilutedSpinGlass

namespace DilutedSpinGlass

theorem weighted_exp_pos {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    0 < ∑ i, w i * Real.exp (f i) :=
  (Real.exp_pos (-‖f‖)).trans_le
    (weighted_exp_bounds w f hw hs (fun i => norm_le_pi_norm f i)).1

/-- Stability before any disorder averaging; no lower bound on the positive
message probabilities or moment condition on the messages occurs. -/
theorem weighted_log_exp_stability {ι : Type*} [Fintype ι] (w f g : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {D : ℝ}
    (hD : ∀ i, |f i-g i| ≤ D) :
    |Real.log (∑ i, w i * Real.exp (f i)) -
      Real.log (∑ i, w i * Real.exp (g i))| ≤ D := by
  have aux (f g : ι → ℝ) (h : ∀ i, f i ≤ g i+D) :
      Real.log (∑ i, w i * Real.exp (f i)) ≤
        Real.log (∑ i, w i * Real.exp (g i)) + D := by
    have hle : (∑ i, w i * Real.exp (f i)) ≤
        (∑ i, w i * Real.exp (g i)) * Real.exp D := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h i)) (hw i))
    have hl := Real.log_le_log (weighted_exp_pos w f hw hs) hle
    rw [Real.log_mul (weighted_exp_pos w g hw hs).ne' (Real.exp_pos D).ne', Real.log_exp] at hl
    exact hl
  have hfg := aux f g (fun i => by have h := (abs_le.mp (hD i)).2; linarith)
  have hgf := aux g f (fun i => by have h := (abs_le.mp (hD i)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end DilutedSpinGlass

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
open _root_.MeasureTheory Set
open scoped NNReal BigOperators

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

noncomputable local instance finiteEncodingDecidableEq_ra22664_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma integral_asProbability {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : FiniteLaw Ω) (f : Ω → X) (g : X → ℝ) :
    ∫ x, g x ∂(P.asProbability f)=P.expect (fun a => g (f a)) := by
  rw [asProbability,integral_atomicProbability]
  rfl

end FiniteLaw

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

lemma piCongrLeft_const_apply {ι κ X : Type} [MeasurableSpace X]
    (e : ι ≃ κ) (x : κ → X) :
    (MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm) x = fun i => x (e i) := by
  funext i
  change (Equiv.piCongrLeft (fun _ : ι => X) e.symm) x i = _
  rw [Equiv.piCongrLeft_apply]
  simp

attribute [local instance] OAI.DilutedSpinGlass.finiteEncodingReindexMeasurableSpace
lemma logMean_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (r : ℕ) (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (eta : ι → Hierarchy r) :
    logMean r (fun x : κ → ℝ => g (fun i => x (e i))) m (fun j => eta (e.symm j)) =
      logMean r g m eta := by
  induction r with
  | zero => simp [logMean]
  | succ r ih =>
    change ι → ProbabilityMeasure (Hierarchy r) at eta
    simp only [logMean]
    congr 2
    have he := (measurePreserving_piCongrLeft
      (fun i : ι => (eta i).toMeasure) e.symm).integral_comp'
        (fun x : ι → Hierarchy r => Real.exp (m 0*logMean r g (fun i => m i.succ) x))
    rw [← he]
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2
    simpa only [Equiv.apply_symm_apply,piCongrLeft_const_apply] using ih (fun i => m i.succ) (fun i => x (e i))

lemma trialLog_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (r : ℕ) (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x : κ → ℝ => g (fun i => x (e i))) = trialLog r ζ m g := by
  change ProbabilityMeasure (Hierarchy r) at ζ
  unfold trialLog
  have he := (measurePreserving_piCongrLeft
    (fun _ : ι => ζ.toMeasure) e.symm).integral_comp' (logMean r g m)
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Equiv.apply_symm_apply,piCongrLeft_const_apply] using logMean_reindex e r g m (fun i => x (e i))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction

lemma q_tanh (x : ℝ) (s : Spin) : q x s=(1+spin s*Real.tanh x)/2 := by
  have hc := (Real.cosh_pos x).ne'
  cases s
  · simp only [q,spin,Bool.false_eq_true,↓reduceIte,mul_neg_one,
      Real.tanh_eq_sinh_div_cosh]
    rw [← Real.cosh_sub_sinh]
    field_simp
    ring
  · simp only [q,spin,↓reduceIte,mul_one,one_mul,Real.tanh_eq_sinh_div_cosh]
    rw [← Real.cosh_add_sinh]
    field_simp

lemma q_artanh (x : ℝ) (hx : x∈Ioo (-1) 1) (s : Spin) :
    q (Real.artanh x) s=(1+spin s*x)/2 := by rw [q_tanh,Real.tanh_artanh hx]

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
open _root_.MeasureTheory
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

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n N : ℕ} {Ω : Type} [Fintype Ω]

lemma SplitMap.prod_range {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A) (g : T.Leaf → ℝ) :
    (∏ a : U.Leaf, g (f.leaf a))=∏ b∈A, g b := by
  classical
  apply Finset.prod_bij (fun a _ => f.leaf a)
  · intro a _; exact (hA _).mp ⟨a,rfl⟩
  · intro a _ b _ he; exact f.injective he
  · intro b hb
    obtain ⟨a,ha⟩ := (hA b).mpr hb
    exact ⟨a,Finset.mem_univ _,ha⟩
  · intro a _; rfl

lemma SplitMap.expect_subsetOverlap {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A)
    (K : KernelTower Ω n) (V : FinitePath Ω n → Fin N → ℝ) (g : ℝ → ℝ) :
    (T.sampleLaw K).expect (fun w => g (subsetOverlap T A V w))=
      (U.sampleLaw K).expect (fun w => g (treeOverlap U V w)) := by
  have he := f.expect_paths K (fun x => g ((∑ i, ∏ a : U.Leaf, V (x a) i)/(N:ℝ)))
  simp_rw [subsetOverlap,treeOverlap,leafProduct_eq_prod]
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply FiniteLaw.expect_congr
  intro w
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact (f.prod_range A hA (fun b => V (T.pathAt b w) i)).symm

omit [Fintype Ω] in
lemma subsetOverlap_bound (T : PrescribedTree n) (A : Finset T.Leaf)
    (V : FinitePath Ω n → Fin N → ℝ) (hV : ∀ x i, |V x i|≤1) (w : Sample Ω T) :
    |subsetOverlap T A V w|≤1 := by
  have hh := FiniteLaw.abs_dot_le_one (fun i => ∏ a∈A, V (T.pathAt a w) i) (fun _ => (1:ℝ))
    (fun index => by rw [Finset.abs_prod]; exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hV _ index))
    (fun _ => by norm_num)
  simpa only [FiniteLaw.dot,subsetOverlap,mul_one] using hh

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubtreePotentialDecidableEq
attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubtreePotentialPropDecidable
lemma subtreePotential_nonneg {L K : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T) (T) :
    0≤ subtreePotential K F T := by
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> first | exact hF _ | rfl

lemma le_subtreePotential {L K : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T)
    {U T : PrescribedTree L} (f : SplitMap U T) (hU : U.leaves≤K) : F U≤ subtreePotential K F T := by
  obtain ⟨S,hS,q,hq,he⟩ := ReducedTopology.exists_bounded_realize U K hU
  subst U
  unfold subtreePotential
  have hn (R : ReducedTopology) (v : R.Vertex → Fin L) :
      0≤(if R.Admissible (fun w => v w) 0 L then
        if Nonempty (SplitMap (R.realize L 0 (fun w => v w)) T) then F (R.realize L 0 (fun w => v w)) else 0 else 0) := by
    split_ifs <;> first | exact hF _ | rfl
  apply le_trans (b := ∑ q : S.Vertex → Fin L, if S.Admissible (fun v => q v) 0 L then
    if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then F (S.realize L 0 (fun v => q v)) else 0 else 0)
  · have hh := Finset.single_le_sum (fun (v : S.Vertex → Fin L) (_ : v∈Finset.univ) => hn S v) (Finset.mem_univ q)
    simpa only [ite_eq_left hq,ite_eq_left (show Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) from ⟨f⟩)] using hh
  · exact Finset.single_le_sum (fun (R : ReducedTopology) (_ : R∈boundedTopologies K) =>
      Finset.sum_nonneg (s := Finset.univ) (fun (v : R.Vertex → Fin L) _ => hn R v)) hS

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TopologyDecay
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
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
lemma expect_pi_map {ι : Type} [Fintype ι] [DecidableEq ι] {α β : ι → Type}
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → β i)
    (g : ((i : ι) → β i) → ℝ) :
    (pi Q).expect (fun a => g (fun i => f i (a i))) =
      (pi (fun i => (Q i).map (f i))).expect g := by
  classical
  have hpoint (a : (i : ι) → α i) :
      g (fun i => f i (a i)) = ∑ b, (∏ i, (if f i (a i)=b i then (1:ℝ) else 0))*g b := by
    have hh (b : (i : ι) → β i) :
        (∏ i, (if f i (a i)=b i then (1:ℝ) else 0)) = if (fun i => f i (a i))=b then 1 else 0 := by
      by_cases h : (fun i => f i (a i))=b
      · subst b; simp
      · rw [ite_eq_right h]
        obtain ⟨i,hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    simp_rw [hh]
    simp
  calc
    _ = (pi Q).expect (fun a => ∑ b, (∏ i, (if f i (a i)=b i then (1:ℝ) else 0))*g b) :=
      (pi Q).expect_congr hpoint
    _ = ∑ b, (∏ i, (Q i).expect (fun a => if f i a=b i then (1:ℝ) else 0))*g b := by
      rw [expect_fintype_sum]
      simp only [expect_mul_right]
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      exact expect_pi_product Q (fun i a => if f i a=b i then 1 else 0)
    _ = _ := rfl

lemma expect_bool (P : FiniteLaw Ω) (v : Ω → Spin) (f : Spin → ℝ) :
    P.expect (fun a => f (v a)) =
      ∑ s : Spin, ((1+spin s * P.expect (fun a => spin (v a)))/2)*f s := by
  have hid (s : Spin) : f s=(f true+f false)/2 + spin s*((f true-f false)/2) := by
    cases s <;> simp [spin] <;> ring
  calc
    _ = P.expect (fun a => (f true+f false)/2 + spin (v a)*((f true-f false)/2)) :=
      P.expect_congr (fun a => hid (v a))
    _ = _ := by simp only [expect_add,expect_const,expect_mul_right,Fintype.sum_bool,spin,
      Bool.false_eq_true,↓reduceIte,neg_one_mul,one_mul]; ring

lemma map_spin_weight (P : FiniteLaw Ω) (v : Ω → Spin)
    (hv : P.expect (fun a => spin (v a)) ∈ Set.Ioo (-1) 1) (s : Spin) :
    (P.map v).weight s=q (Real.artanh (P.expect (fun a => spin (v a)))) s := by
  classical
  dsimp only [map]
  have hc : (fun a : Ω => @ite ℝ (v a=s) (finiteMapDecEq Spin (v a) s) 1 0) =
      (fun a : Ω => if v a=s then (1:ℝ) else 0) := by funext a; split_ifs <;> rfl
  rw [hc]
  rw [expect_bool P v (fun t => if t=s then 1 else 0),q_artanh _ hv]
  simp

lemma logMean_pi_spin {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] (Q : (i : ι) → FiniteLaw (α i))
    (v : (i : ι) → α i → Spin) (F : (ι → Spin) → ℝ)
    (hv : ∀ i, (Q i).expect (fun a => spin (v i a)) ∈ Set.Ioo (-1) 1) :
    (pi Q).logMean 1 (fun a => F (fun i => v i (a i))) =
      spinLog F (fun i => Real.artanh ((Q i).expect (fun a => spin (v i a)))) := by
  change Real.log ((pi Q).expect (fun a => Real.exp (1*F (fun i => v i (a i)))))/1=_
  simp only [one_mul,div_one]
  rw [expect_pi_map Q v (fun s => Real.exp (F s))]
  simp only [expect,pi,map_spin_weight _ _ (hv _),spinLog]
  congr 1
  congr!

end FiniteLaw
end DilutedSpinGlass

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

noncomputable local instance physicalSubtreeConcentrationDecidableEq_ra22664_1 (type : Type) :
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

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootOverlapDeviation
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

lemma SplitMap.subsetDeviation_eq (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A)
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) :
    subsetDeviation μ Ω T A K V=overlapDeviation μ Ω U K V := by
  unfold subsetDeviation overlapDeviation FiniteLaw.mixedDeviation
  have hm (z : Z) := f.expect_subsetOverlap A hA (K z) (V z) id
  simp only [id_eq] at hm
  simp_rw [hm]
  apply integral_congr_ae
  exact ae_of_all μ (fun z => f.expect_subsetOverlap A hA (K z) (V z)
    (fun x => |x-(∫ y, (U.sampleLaw (K y)).expect (treeOverlap U (V y)) ∂μ)|))

end DilutedSpinGlass.PrescribedTree

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

include hb hV in
lemma integrable_rootOverlapCenteredAbs (c : ℝ) : Integrable (fun z : FullRootState Y X I M =>
    (S.sampleLaw (rootTower T Q m base old z)).expect
      (fun w => |treeOverlap S (rootVector V z) w-c|)) μ := by
  have he (z : FullRootState Y X I M) :
      (S.sampleLaw (rootTower T Q m base old z)).expect
        (fun w => |treeOverlap S (rootVector V z) w-c|)=
      rootTreeMean S T Q m base old (fun x => |spatialProduct (fun _ : S.Leaf => V) x-c|) z := by
    unfold rootTreeMean packRoot
    apply FiniteLaw.expect_congr
    intro w
    rw [treeOverlap_eq_spatialProduct]
    rfl
  simp_rw [he]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1+|c|)
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (add_le_add (spatialProduct_bound _ (fun _ => hV) x) le_rfl)

include hb hV in
lemma root_overlapDeviation_le_variance {t : ℝ} (ht : 0<t) :
    overlapDeviation μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V) ≤
      overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V)/(2*t)+t/2 := by
  apply FiniteLaw.mixedDeviation_le_variance
  · simpa using integrable_rootOverlapMoment S T Q m base old V hb μ hV 1
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2
  · exact integrable_rootOverlapCenteredAbs S T Q m base old V hb μ hV _
  · exact ht

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QSubsetDeviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory ReducedTopology Filter
open scoped BigOperators Topology
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubsetDeviationDecidableEq
attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubsetDeviationDecidable
lemma shapeDeviation_nonneg (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) :
    0 ≤ shapeDeviation μ Ω S K V := by
  apply Finset.sum_nonneg
  intro A _
  split_ifs
  · exact FiniteLaw.mixedDeviation_nonneg _ _ _ _
  · rfl

lemma shapeDeviation_le_subtree (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (F : PrescribedTree n → ℝ) (hF : ∀ S, 0≤F S) {t : ℝ} (ht : 0<t)
    (hdev : ∀ S, overlapDeviation μ Ω S K V≤F S/(2*t)+t/2)
    (S : PrescribedTree n) (b : ℕ) (hS : S.leaves=b) :
    shapeDeviation μ Ω S K V ≤ (2:ℝ)^b*(subtreePotential b F S/(2*t)+t/2) := by
  have hle (A : Finset S.Leaf) :
      (if A.Nonempty then subsetDeviation μ Ω S A K V else 0)≤ subtreePotential b F S/(2*t)+t/2 := by
    by_cases ha : A.Nonempty
    · rw [ite_eq_left ha]
      obtain ⟨U,f,hf⟩ := exists_subset_tree S A ha
      rw [f.subsetDeviation_eq μ Ω A hf K V]
      apply (hdev U).trans
      exact add_le_add (div_le_div_of_nonneg_right
        (le_subtreePotential F hF f (f.leaves_le.trans_eq hS)) (by positivity)) le_rfl
    · rw [ite_eq_right ha]
      have := subtreePotential_nonneg F hF S (K := b)
      positivity
  unfold shapeDeviation
  apply (Finset.sum_le_sum (fun A _ => hle A)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,card_leaf,hS,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]

lemma qExpect_add {n : ℕ} (m : Fin (n+1) → ℝ) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T+G T) k S=qExpect m F k S+qExpect m G k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,mul_add,Finset.sum_add_distrib]

lemma qExpect_div_const {n : ℕ} (m : Fin (n+1) → ℝ) (F : PrescribedTree n → ℝ)
    (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T/c) k S=qExpect m F k S/c := by
  simpa only [div_eq_mul_inv] using qExpect_mul_const m F c⁻¹ k S

lemma subtreePotential_le_card {L b : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ S, F S≤1)
    (S : PrescribedTree L) : subtreePotential b F S≤
      ∑ R∈boundedTopologies b, (Fintype.card (R.Vertex → Fin L):ℝ) := by
  unfold subtreePotential
  apply Finset.sum_le_sum
  intro R _
  calc
    _ ≤ ∑ _q : R.Vertex → Fin L, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro q _
      split_ifs <;> first | exact hF _ | norm_num
    _ = _ := by simp

lemma qExpect_subtree_bounded {L : ℕ} [NeZero L] (b k : ℕ)
    (F : ℕ → PrescribedTree L → ℝ) (hF : ∀ n S, F n S≤1) :
    IsBoundedUnder (·≤·) atTop (fun n => qExpect (grid L 0 L) (subtreePotential b (F n)) k (single L)) := by
  apply isBoundedUnder_of_eventually_le (a := ∑ R∈boundedTopologies b, (Fintype.card (R.Vertex → Fin L):ℝ))
  apply Eventually.of_forall
  intro n
  have hh := qExpect_mono (grid L 0 L) (grid_strictMono (NeZero.pos L)).monotone grid_nonneg
    (fun S => subtreePotential_le_card (F n) (hF n) S (b := b)) k (single L)
  simpa only [qExpect_const _ (show grid L 0 L 0=0 by simp [grid]) (grid_last (NeZero.pos L))] using hh

lemma qExpect_shapeDeviation_le {L : ℕ} [NeZero L]
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ)
    (F : PrescribedTree L → ℝ) (hF : ∀ S, 0≤F S) {t : ℝ} (ht : 0<t)
    (hdev : ∀ S, overlapDeviation μ Ω S K V≤F S/(2*t)+t/2) (k : ℕ) :
    qExpect (grid L 0 L) (fun S => shapeDeviation μ Ω S K V) k (single L) ≤
      (2:ℝ)^(k+1)*(qExpect (grid L 0 L) (subtreePotential (k+1) F) k (single L)/(2*t)+t/2) := by
  have hh := qExpect_mono_leaves (grid L 0 L) (grid_strictMono (NeZero.pos L)).monotone grid_nonneg
    (fun S => shapeDeviation μ Ω S K V)
    (fun S => (subtreePotential (k+1) F S/(2*t)+t/2)*(2:ℝ)^(k+1)) k (single L)
    (fun S hS => by
      rw [leaves_single] at hS
      have he : S.leaves=k+1 := by omega
      simpa only [mul_comm] using shapeDeviation_le_subtree μ Ω K V F hF ht hdev S (k+1) he)
  rw [qExpect_mul_const,qExpect_add,qExpect_div_const,
    qExpect_const _ (show grid L 0 L 0=0 by simp [grid]) (grid_last (NeZero.pos L))] at hh
  simpa only [mul_comm] using hh

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalShapeError
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

noncomputable local instance physicalShapeErrorDecidableEq_ra22664_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma physicalTreeDeviation_le_variance (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) {t : ℝ} (ht : 0<t) :
    physicalTreeDeviation M C H N L u T ≤ physicalTreeVariance M C H N L u T/(2*t)+t/2 := by
  unfold physicalTreeDeviation physicalTreeVariance
  exact root_overlapDeviation_le_variance _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i) ht

lemma physicalShapeDeviation_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    0 ≤ physicalShapeDeviation M C H N L u T := shapeDeviation_nonneg _ _ _ _ _

lemma physicalShapeDeviation_qExpect_le (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) {t : ℝ} (ht : 0<t) (k : ℕ) :
    qExpect (grid (L+1) 0 (L+1)) (physicalShapeDeviation M C H N L u) k (single (L+1)) ≤
      (2:ℝ)^(k+1)*(qExpect (grid (L+1) 0 (L+1))
        (subtreePotential (k+1) (physicalTreeVariance M C H N L u)) k (single (L+1))/(2*t)+t/2) := by
  apply qExpect_shapeDeviation_le _ _ _ _ _ (physicalTreeVariance_nonneg M C H N L u) ht
  exact fun T => physicalTreeDeviation_le_variance M C H N L u T ht

/-- The complete finite-shape MAD error for the actual selected reservoir tends
 to zero. This is the error required by the empirical pattern comparison. -/
theorem physicalShapeError_tendsto (M : Model p) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (physicalShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))) atTop)
      atTop (𝓝 0) := by
  apply doubleLimit_young _ (fun L n => qExpect (grid (L+1) 0 (L+1))
    (subtreePotential (k+1) (physicalTreeVariance M C H (Ns L n+1) L (us L n)))
    k (single (L+1))) ((2:ℝ)^(k+1)) (by positivity)
  · intro L n
    exact qExpect_nonneg _ (grid_strictMono (by omega)).monotone grid_nonneg
      _ (physicalShapeDeviation_nonneg _ _ _ _ _ _) _ _
  · intro L
    exact qExpect_subtree_bounded (k+1) k _ (fun _ _ => physicalTreeVariance_le_one _ _ _ _ _ _ _)
  · intro t ht L n
    exact physicalShapeDeviation_qExpect_le _ _ _ _ _ _ ht k
  · exact physicalSubtree_limsup_tendsto M C H Ns us hcontrol (k+1) k

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped Topology BigOperators
namespace FiniteLaw
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (Q : (z : Z) → FiniteLaw (Ω z))
    (f : (z : Z) → Ω z → ℝ)
lemma mixedDeviation_le_two (hf : ∀ z x, |f z x|≤1) : mixedDeviation μ Ω Q f≤2 := by
  have he : |∫ z, (Q z).expect (f z) ∂μ|≤1 :=
    abs_integral_le_bound (fun z => (Q z).abs_expect_le (hf z))
  apply (le_abs_self _).trans
  apply abs_integral_le_bound
  intro z
  apply (Q z).abs_expect_le
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (by linarith [hf z x])
end FiniteLaw
namespace PrescribedTree
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}
lemma shapeDeviation_bound (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (S : PrescribedTree n)
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (hV : ∀ z y i, |V z y i|≤1) : shapeDeviation μ Ω S K V≤(2:ℝ)^S.leaves*2 := by
  classical
  unfold shapeDeviation
  calc
    _ ≤ ∑ _A : Finset S.Leaf, (2:ℝ) := by
      apply Finset.sum_le_sum
      intro A _
      split_ifs
      · exact FiniteLaw.mixedDeviation_le_two μ _ _ _
          (fun z w => subsetOverlap_bound S A (V z) (hV z) w)
      · norm_num
    _ = _ := by simp [card_leaf]

lemma qExpect_shape_bound {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (F : PrescribedTree n → ℝ) (hF : ∀ S, F S≤(2:ℝ)^S.leaves*2)
    (k : ℕ) : qExpect m F k (single n) ≤ (2:ℝ)^(k+1)*2 := by
  have hh := qExpect_mono_leaves m hm hpos F (fun _ => (2:ℝ)^(k+1)*2) k (single n)
    (fun S hS => by simpa only [hS,leaves_single,Nat.add_comm 1 k] using hF S)
  simpa only [qExpect_const m hroot hend] using hh
end PrescribedTree

lemma limsup_le_of_vanishing_error (f g e : ℕ → ℝ)
    (hf : ∀ n, 0≤f n) (hg : IsBoundedUnder (·≤·) atTop g)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ n, f n≤g n+e n) :
    limsup f atTop≤limsup g atTop := by
  have hle (t : ℝ) (ht : 0<t) : limsup f atTop≤limsup g atTop+2*t := by
    have hgf : ∀ᶠ n in atTop, g n<limsup g atTop+t :=
      eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht) hg
    have hef : ∀ᶠ n in atTop, e n<t := he.eventually (Iio_mem_nhds ht)
    apply limsup_le_of_le (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall hf).frequently))
    filter_upwards [hgf,hef] with n hgn hen
    linarith [h n]
  have hc : ContinuousAt (fun t : ℝ => limsup g atTop+2*t) 0 := by fun_prop
  have hh := ge_of_tendsto (hc.continuousWithinAt.tendsto (s := Set.Ioi 0))
    (eventually_nhdsWithin_of_forall (fun t ht => hle t ht))
  simpa using hh
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalInterior
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

lemma exists_weight_pos (P : FiniteLaw Ω) : ∃ a, 0<P.weight a := by
  by_contra! h
  have hh := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => h a)
  rw [P.total] at hh
  simp only [Finset.sum_const_zero] at hh
  linarith

lemma tilt_weight_pos (P : FiniteLaw Ω) (m : ℝ) (f : Ω → ℝ)
    (a : Ω) (ha : 0<P.weight a) : 0<(P.tilt m f).weight a :=
  div_pos (mul_pos ha (Real.exp_pos _)) (P.expMoment_pos _ _)

lemma expect_lt_const (P : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ a, f a ≤ c) (hg : ∃ a, 0<P.weight a ∧ f a < c) : P.expect f < c := by
  rw [← P.expect_const c]
  unfold expect
  apply Finset.sum_lt_sum
  · intro a _
    exact mul_le_mul_of_nonneg_left (hf a) (P.nonneg a)
  · obtain ⟨a,ha,hfa⟩ := hg
    exact ⟨a,Finset.mem_univ _,mul_lt_mul_of_pos_left hfa ha⟩

lemma spinMean_interior (P : FiniteLaw Ω) (s : Ω → ℝ) (hs : ∀ a, |s a|≤1)
    (hl : ∃ a, 0<P.weight a ∧ s a<1) (hu : ∃ a, 0<P.weight a ∧ -1 < s a) :
    P.expect s ∈ Set.Ioo (-1) 1 := by
  refine ⟨?_, P.expect_lt_const s 1 (fun a => (abs_le.mp (hs a)).2) hl⟩
  have hh := P.expect_lt_const (fun a => -s a) 1
    (fun a => by have := (abs_le.mp (hs a)).1; linarith) ?_
  · rw [P.expect_neg] at hh
    linarith
  · obtain ⟨a,ha,hsa⟩ := hu
    exact ⟨a,ha,by linarith⟩

lemma bind_tilt_spinMean_interior {Γ : Type} [Fintype Γ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Γ) (m : ℝ) (f : Ω×Γ → ℝ) (s : Ω → ℝ)
    (hs : ∀ a, |s a|≤1) (hl : ∃ a, 0<P.weight a ∧ s a<1)
    (hu : ∃ a, 0<P.weight a ∧ -1 < s a) :
    ((P.bind (fun _ => Q)).tilt m f).expect (fun a => s a.1) ∈ Set.Ioo (-1) 1 := by
  obtain ⟨b,hb⟩ := Q.exists_weight_pos
  apply spinMean_interior ((P.bind (fun _ => Q)).tilt m f) (fun a : Ω×Γ => s a.1) (fun a => hs a.1)
  · obtain ⟨a,ha,hsa⟩ := hl
    exact ⟨(a,b),tilt_weight_pos _ _ _ _ (mul_pos ha hb),hsa⟩
  · obtain ⟨a,ha,hsa⟩ := hu
    exact ⟨(a,b),tilt_weight_pos _ _ _ _ (mul_pos ha hb),hsa⟩

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- Finite physical full support survives every old marked factor and every
 sequential tilt, even when the auxiliary priors have zero masses. -/
lemma terminalInterior_tilted (r : ℕ) {k : ℕ} (roots : Fin k → I)
    (P : FiniteLaw Ω) (a : Ω) (Q : (i : I) → Fin (r+1) → FiniteLaw (A i))
    (m : Fin (r+1) → ℝ) (f : FinitePath (Ω×Row roots) (r+1) → ℝ)
    (s : Ω → ℝ) (hs : ∀ x, |s x|≤1)
    (hl : ∃ x, 0<P.weight x ∧ s x<1) (hu : ∃ x, 0<P.weight x ∧ -1 < s x) :
    TerminalInterior r (tilt (r+1) (tower roots (r+1) (terminalTower a P r) Q) m f)
      (fun y => s (terminalState r (physical roots (r+1) y))) := by
  induction r with
  | zero =>
    exact FiniteLaw.bind_tilt_spinMean_interior P (FiniteLaw.pi (fun j => Q (roots j) 0))
      (m 0) (fun x => f (x,())) s hs hl hu
  | succ r ih =>
    intro x
    exact ih (fun i j => Q i j.succ) (fun j => m j.succ) (fun y => f (x,y))

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalEncodingInterior
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open ConcreteReservoir UniversalDictionary HeterogeneousMarks KernelTower
open scoped BigOperators

noncomputable local instance instDecidableEq_solutions_ra22664_1 (β : Type) : DecidableEq β := Classical.decEq β
lemma uniform_spinMean_hypotheses {N : ℕ} (hN : 0<N) (i : Site N) :
    (∃ σ : Fin N → Spin, 0<(FiniteLaw.uniform : FiniteLaw (Fin N → Spin)).weight σ ∧
      spin (readSpin σ i)<1) ∧
    (∃ σ : Fin N → Spin, 0<(FiniteLaw.uniform : FiniteLaw (Fin N → Spin)).weight σ ∧
      -1 < spin (readSpin σ i)) := by
  have hw (σ : Fin N → Spin) : 0<(FiniteLaw.uniform : FiniteLaw (Fin N → Spin)).weight σ := by
    simp only [FiniteLaw.uniform]
    positivity
  constructor
  · refine ⟨fun _ => false,hw _,?_⟩
    rw [readSpin_eq hN]
    norm_num [spin]
  · refine ⟨fun _ => true,hw _,?_⟩
    rw [readSpin_eq hN]
    norm_num [spin]

lemma terminalInterior_rootTower {N r : ℕ} (hN : 0<N)
    {I X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)] {M : ℕ}
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath (Fin N → Spin) (r+1) → ℝ)
    (old : (i : I) → FinitePath (Fin N → Spin) (r+1) → FinitePath (A i) (r+1) → ℝ)
    (z : FullRootState Y X I M) (i : Site N) :
    TerminalInterior r
      (rootTower (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m base old z)
      (fun y => rootVector (readVector (fun v x => readSpin (terminalState r x) v)) z y i) := by
  obtain ⟨hl,hu⟩ := uniform_spinMean_hypotheses hN i
  exact terminalInterior_tilted r (rootArray z.2.2.1 z.2.2.2) FiniteLaw.uniform
    (fun _ : Fin N => false) Q m _ (fun σ => spin (readSpin σ i))
    (fun σ => (abs_spin _).le) hl hu

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductTower
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.productTowerMeasurableSpace
local instance productTowerBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
namespace KernelTower
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]


attribute [local instance] OAI.DilutedSpinGlass.productTowerMeasurableSpace
lemma backwardLog_encode (r : ℕ) (T : (i : ι) → KernelTower (α i) (r+1))
    (V : (i : ι) → FinitePath (α i) (r+1) → Spin) (F : (ι → Spin) → ℝ)
    (m : Fin (r+1) → ℝ) (hm : m (Fin.last r)=1)
    (hV : ∀ i, TerminalInterior r (T i) (fun y => spin (V i y))) :
    backwardLog (r+1) (pi (r+1) T) m
      (fun y => F (fun i => V i (FinitePath.proj (r+1) y i))) =
    DilutedSpinGlass.logMean r (FiniteLaw.spinLog F) (fun i => m i.castSucc)
      (fun i => encode r (T i) (fun y => spin (V i y))) := by
  induction r with
  | zero =>
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun a => F (fun i => V i (a i,()))) =
      FiniteLaw.spinLog F (fun i => Real.artanh ((T i).1.expect (fun a => spin (V i (a,())))))
    rw [show m 0=1 from hm]
    exact FiniteLaw.logMean_pi_spin _ _ F hV
  | succ r ih =>
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun a => backwardLog (r+1) (pi (r+1) (fun i => (T i).2 (a i)))
        (fun j => m j.succ)
        (fun y => F (fun i => V i (a i,FinitePath.proj (r+1) y i)))) = _
    have hc (a : (i : ι) → α i) := ih (fun i => (T i).2 (a i))
      (fun i y => V i (a i,y)) (fun j => m j.succ)
      (by simpa only [Fin.succ_last] using hm) (fun i => hV i (a i))
    simp_rw [hc]
    change Real.log ((FiniteLaw.pi (fun i => (T i).1)).expect
      (fun a => Real.exp (m 0 * DilutedSpinGlass.logMean r (FiniteLaw.spinLog F)
        (fun j => m j.castSucc.succ) (fun i => encode r ((T i).2 (a i))
          (fun y => spin (V i (a i,y))))))) / m 0 =
      Real.log (∫ x, Real.exp (m 0 * DilutedSpinGlass.logMean r (FiniteLaw.spinLog F)
        (fun j => m j.succ.castSucc) x)
        ∂Measure.pi (fun i => ((T i).1.asProbability
          (fun a => encode r ((T i).2 a) (fun y => spin (V i (a,y))))).toMeasure)) / m 0
    rw [FiniteLaw.integral_pi_asProbability]
    rfl

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinLogContinuous
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {ι : Type} [Fintype ι]
lemma spinLog_bound (F : (ι → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C) (x : ι → ℝ) :
    |spinLog F x|≤C := by
  classical
  apply weighted_log_exp_bound _ _ (fun s => (Finset.prod_pos (fun i _ => q_pos _ _)).le) _ hF
  rw [← Fintype.prod_sum]
  simp only [q_sum, Finset.prod_const_one]
lemma spinLog_continuous (F : (ι → Spin) → ℝ) : Continuous (spinLog F) := by
  classical
  apply Continuous.log
  · exact continuous_finsetSum _ (fun s _ =>
      (continuous_finsetProd _ (fun i _ => (continuous_q (s i)).comp (continuous_apply i))).mul_const _)
  · intro x
    apply ne_of_gt
    exact Finset.sum_pos (fun s _ => mul_pos (Finset.prod_pos (fun i _ => q_pos _ _)) (Real.exp_pos _))
      Finset.univ_nonempty
end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixedPatterns
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.HeterogeneousMarks.rootInsertionMeasurableSpace
local instance rootInsertionBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    Measurable (rootInsertion T Q m base old V a F) := by
  apply measurable_from_prod_countable_left
  intro v
  apply measurable_packRoot_into (F := fun h k x n y =>
    backwardLog (L+1) (tilt (L+1) (tower (rootArray n y) (L+1) T Q) m
      (logWeight (base h k x) (rootArray n y) old)) m
      (fun w => F (fun i => V (physical (rootArray n y) (L+1) w) (v i))))
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  simp_rw [← insertion]
  apply Measurable.sub
  · apply measurable_backwardLog (L+1) (tower (rootArray n y) (L+1) T Q) m
    intro w
    exact ((hb k _).add measurable_const).add measurable_const
  · apply measurable_backwardLog (L+1) (tower (rootArray n y) (L+1) T Q) m
    intro w
    exact (hb k _).add measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentInsertion_encode (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (hm : m (Fin.last L)=1)
    (hV : ∀ z i, TerminalInterior L (rootTower T Q m base old z)
      (fun y => rootVector (fun w j => spin (V w j)) z y i))
    (z : Fin a → FullRootState Y X I M × Site N) :
    independentInsertion T Q m base old V a F z =
      DilutedSpinGlass.logMean L (FiniteLaw.spinLog F) (fun i => m i.castSucc)
        (fun i => rootEncoding T Q m base old (fun w j => spin (V w j)) (z i).1 (z i).2) :=
  backwardLog_encode (α := fun i : Fin a => rootAlphabet (Ω := Ω) (A := A) (z i).1) L
    (fun i => rootTower T Q m base old (z i).1)
    (fun i y => V (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) (L+1) y) (z i).2)
    F m hm (fun i => hV (z i).1 (z i).2)

include hb in
lemma measurable_independentInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (hm : ∀ i, 0 < m i) (hend : m (Fin.last L)=1)
    (hV : ∀ z i, TerminalInterior L (rootTower T Q m base old z)
      (fun y => rootVector (fun w j => spin (V w j)) z y i)) :
    Measurable (independentInsertion T Q m base old V a F) := by
  have hf : ∀ s, |F s|≤∑ t, |F t| := fun s => Finset.single_le_sum (fun t _ => abs_nonneg (F t)) (Finset.mem_univ s)
  have hc := (logMean_continuous_bound L _ (FiniteLaw.spinLog_continuous F)
    (FiniteLaw.spinLog_bound F hf) (fun i => m i.castSucc) (fun i => hm i.castSucc)).1
  simp_rw [show independentInsertion T Q m base old V a F = fun z =>
      DilutedSpinGlass.logMean L (FiniteLaw.spinLog F) (fun i => m i.castSucc)
        (fun i => rootEncoding T Q m base old (fun w j => spin (V w j)) (z i).1 (z i).2) from
    funext (independentInsertion_encode T Q m base old V a F hend hV)]
  exact hc.measurable.comp (Measurable.of_eval (fun index =>
    (measurable_rootEncoding_joint T Q m base old (fun w j => spin (V w j)) hb).comp (measurable_pi_apply index)))
end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass.Pattern
open _root_.MeasureTheory
open scoped BigOperators
noncomputable local instance mixedPatternsDecidableEq_ra22664_1 (type : Type) :
    DecidableEq type := Classical.decEq type
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (P : (z : Z) → FiniteLaw (Ω z))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (mass : (z : Z) → Ω z → (ι → Bool) → ℝ)
    (hmass : ∀ z w e, 0 ≤ mass z w e) (htotal : ∀ z w, ∑ e, mass z w e=1)
    (hmean : ∀ e, Measurable (fun z => (P z).expect (fun w => mass z w e)))

omit [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] in
include hmass in
lemma mixedMass_nonneg (e : ι → Bool) : 0 ≤ mixedMass μ Ω P mass e :=
  integral_nonneg (fun z => (P z).expect_nonneg (fun w => hmass z w e))

include hmass htotal hmean in
lemma mixedMass_total : ∑ e, mixedMass μ Ω P mass e=1 := by
  have hi (e : ι → Bool) : Integrable (fun z => (P z).expect (fun w => mass z w e)) μ :=
    bounded_integrable (hmean e) (fun z => (P z).abs_expect_le (fun w => by
      rw [abs_of_nonneg (hmass z w e)]
      exact mass_le_one _ (hmass z w) (htotal z w) e))
  unfold mixedMass
  rw [← integral_finsetSum _ (fun e _ => hi e)]
  simp_rw [← FiniteLaw.expect_fintype_sum,htotal,FiniteLaw.expect_const]
  simp

include hmass htotal hmean in
lemma mixedMass_moment (S : Finset ι) :
    moment (mixedMass μ Ω P mass) S=∫ z, (P z).expect (fun w => moment (mass z w) S) ∂μ := by
  have hi (e : ι → Bool) : Integrable (fun z => (P z).expect (fun w => mass z w e)) μ :=
    bounded_integrable (hmean e) (fun z => (P z).abs_expect_le (fun w => by
      rw [abs_of_nonneg (hmass z w e)]
      exact mass_le_one _ (hmass z w) (htotal z w) e))
  simp only [moment,mixedMass,← integral_mul_const,FiniteLaw.expect_fintype_sum,
    FiniteLaw.expect_mul_right]
  exact (integral_finsetSum _ (fun e _ => (hi e).mul_const _)).symm

include hmass htotal hmean in
 
lemma mixed_pattern_replacement (a : ℕ) (f : (Fin a → (ι → Bool)) → ℝ)
    (hf : ∀ x, |f x|≤1)
    (hA : Measurable (fun z => (P z).expect (fun w => ∑ x, (∏ i, mass z w (x i))*f x)))
    (hD : ∀ S : Finset ι, Measurable (fun z => (P z).expect (fun w =>
      |moment (mass z w) S-moment (mixedMass μ Ω P mass) S|))) :
    |(∫ z, (P z).expect (fun w => ∑ x, (∏ i, mass z w (x i))*f x) ∂μ)-
      (∑ x, (∏ i, mixedMass μ Ω P mass (x i))*f x)| ≤
      (a:ℝ)*∑ S∈(Finset.univ : Finset (Finset ι)).erase ∅,
        FiniteLaw.mixedDeviation μ Ω P (fun z w => moment (mass z w) S) := by
  let Q := mixedMass μ Ω P mass
  let A (z : Z) (w : Ω z) := ∑ x, (∏ i, mass z w (x i))*f x
  let B := ∑ x, (∏ i, Q (x i))*f x
  have hQ := mixedMass_nonneg μ Ω P mass hmass
  have htQ := mixedMass_total μ Ω P mass hmass htotal hmean
  have hAb (z : Z) (w : Ω z) : |A z w|≤1 := by
    apply mass_abs_average _ f (fun x => Finset.prod_nonneg (fun i _ => hmass z w (x i))) _ hf
    rw [← Fintype.prod_sum]
    simp only [htotal,Finset.prod_const_one]
  have hAi : Integrable (fun z => (P z).expect (A z)) μ :=
    bounded_integrable hA (fun z => (P z).abs_expect_le (hAb z))
  have hDb (S : Finset ι) (z : Z) (w : Ω z) :
      |moment (mass z w) S-moment Q S|≤2 := by
    apply (abs_sub _ _).trans
    have h1 := mass_abs_average _ _ (hmass z w) (htotal z w) (fun x => (abs_character S x).le)
    have h2 := mass_abs_average _ _ hQ htQ (fun x => (abs_character S x).le)
    change |moment (mass z w) S|≤1 at h1
    change |moment Q S|≤1 at h2
    linarith
  have hDi (S : Finset ι) : Integrable (fun z => (P z).expect
      (fun w => |moment (mass z w) S-moment Q S|)) μ :=
    bounded_integrable (hD S) (fun z => (P z).abs_expect_le (fun w => by
      rw [abs_abs]; exact hDb S z w))
  change |(∫ z, (P z).expect (A z) ∂μ)-B|≤_
  have hBc : (∫ _ : Z, B ∂μ)=B := by simp
  rw [← hBc,← integral_sub hAi (integrable_const B)]
  calc
    _ ≤ ∫ z, |(P z).expect (A z)-B| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z, (a:ℝ)*∑ S∈(Finset.univ : Finset (Finset ι)).erase ∅,
        (P z).expect (fun w => |moment (mass z w) S-moment Q S|) ∂μ := by
      apply integral_mono (hAi.sub (integrable_const B)).abs
        ((integrable_finsetSum _ (fun S _ => hDi S)).const_mul _) 
      intro z
      dsimp only [Pi.sub_apply]
      rw [← (P z).expect_const B,← FiniteLaw.expect_sub]
      calc
        _ ≤ (P z).expect (fun w => |A z w-B|) := FiniteLaw.abs_expect_le_expect_abs _ _
        _ ≤ (P z).expect (fun w => (a:ℝ)*∑ S∈(Finset.univ : Finset (Finset ι)).erase ∅,
            |moment (mass z w) S-moment Q S|) :=
          (P z).expect_mono (fun w => pattern_replacement _ _ (hmass z w) hQ (htotal z w) htQ a f hf)
        _ = _ := by rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_sum]
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun S _ => hDi S)]
      congr 1
      apply Finset.sum_congr rfl
      intro S _
      rw [mixedMass_moment μ Ω P mass hmass htotal hmean]
      rfl

end DilutedSpinGlass.Pattern

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_BranchingEvaluation
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
lemma branchingProduct_eq_prod {n : ℕ} (S : PrescribedTree n)
    (F : S.Leaf → FinitePath Ω n → ℝ) (z : Sample Ω S) :
    branchingProduct S F z=∏ a, F a (pathAt S a z) := by
  induction S with
  | leaf => change F () ()=∏ a : Unit, F a (); simp
  | @node _ k C ih =>
    change (∏ j, branchingProduct (C j) (fun b y => F ⟨j,b⟩ ((z j).1,y)) (z j).2)=_
    change _=(∏ a : (j : Fin k) × (C j).Leaf, F a (pathAt (.node k C) a z))
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl (fun j _ => ih j _ (z j).2)

lemma branchingMean_eq_expect {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (F : S.Leaf → FinitePath Ω n → ℝ) :
    branchingMean S T F=(sampleLaw S T).expect (branchingProduct S F) := by
  induction S with
  | leaf => exact ((sampleLaw .leaf T).expect_const (F () ())).symm
  | @node n k C ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω n) at T
    rcases T with ⟨P,Q⟩
    change (((j : Fin k) × (C j).Leaf) → (Ω × FinitePath Ω n) → ℝ) at F
    change (∏ i, P.expect (fun a => branchingMean (C i) (Q a) (fun b y => F ⟨i,b⟩ (a,y)))) =
      (FiniteLaw.pi (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))).expect
        (fun z => ∏ i, branchingProduct (C i) (fun b y => F ⟨i,b⟩ ((z i).1,y)) (z i).2)
    rw [FiniteLaw.expect_pi_product (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))
      (fun i (z : Ω × Sample Ω (C i)) => branchingProduct (C i) (fun b y => F ⟨i,b⟩ (z.1,y)) z.2)]
    apply Finset.prod_congr rfl
    intro i _
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact ih i (Q a) _

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
lemma branchingMean_pi {n : ℕ} (S : PrescribedTree n) (T : (i : ι) → KernelTower (α i) n)
    (F : (i : ι) → S.Leaf → FinitePath (α i) n → ℝ) :
    branchingMean S (KernelTower.pi n T)
      (fun a y => ∏ i, F i a (FinitePath.proj n y i)) =
      ∏ i, branchingMean S (T i) (F i) := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    change ((i : ι) → FiniteLaw (α i) × (α i → KernelTower (α i) n)) at T
    change ((i : ι) → ((j : Fin k) × (C j).Leaf) → (α i × FinitePath (α i) n) → ℝ) at F
    change (∏ j, (FiniteLaw.pi (fun i => (T i).1)).expect
      (fun a => branchingMean (C j) (KernelTower.pi n (fun i => (T i).2 (a i)))
        (fun b y => ∏ i, F i ⟨j,b⟩ (a i,FinitePath.proj n y i)))) =
      ∏ i, ∏ j, (T i).1.expect (fun a => branchingMean (C j) ((T i).2 a) (fun b y => F i ⟨j,b⟩ (a,y)))
    have he (j) (a : (i : ι) → α i) := ih j
      (fun i => (T i).2 (a i)) (fun i b y => F i ⟨j,b⟩ (a i,y))
    simp_rw [he]
    have hp (j) := FiniteLaw.expect_pi_product (fun i => (T i).1)
      (fun i a => branchingMean (C j) ((T i).2 a) (fun b y => F i ⟨j,b⟩ (a,y)))
    simp_rw [hp]
    exact Finset.prod_comm

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductPatterns
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators

lemma function_indicator_product {ι : Type} [Fintype ι] {β : ι → Type} [∀ i, DecidableEq (β i)]
    (f g : (i : ι) → β i) :
    (if f=g then (1:ℝ) else 0)=∏ i, if f i=g i then (1:ℝ) else 0 := by
  by_cases h : f=g
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

namespace PrescribedTree
variable {Ω : Type} [Fintype Ω]

lemma patternMass_eq_branchingMean {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (V : FinitePath Ω n → Spin) (e : S.Leaf → Spin) :
    patternMass S T V e = branchingMean S T (fun a y => if V y=e a then 1 else 0) := by
  rw [branchingMean_eq_expect]
  unfold patternMass
  apply FiniteLaw.expect_congr
  intro z
  rw [branchingProduct_eq_prod]
  exact function_indicator_product (ι := S.Leaf) (fun a => V (pathAt S a z)) e

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]

lemma patternMass_pi {n : ℕ} (S : PrescribedTree n) (T : (i : ι) → KernelTower (α i) n)
    (V : (i : ι) → FinitePath (α i) n → Spin) (e : ι → S.Leaf → Spin) :
    (sampleLaw S (KernelTower.pi n T)).expect (fun z =>
      if (fun i a => V i (FinitePath.proj n (pathAt S a z) i))=e then 1 else 0) =
      ∏ i, patternMass S (T i) (V i) (e i) := by
  have hid (z : Sample ((i : ι) → α i) S) :
      (if (fun i a => V i (FinitePath.proj n (pathAt S a z) i))=e then (1:ℝ) else 0) =
      branchingProduct S
        (fun a y => ∏ i, if V i (FinitePath.proj n y i)=e i a then (1:ℝ) else 0) z := by
    rw [function_indicator_product (ι := ι) (fun i a => V i (FinitePath.proj n (pathAt S a z) i)) e]
    simp_rw [function_indicator_product (ι := S.Leaf)]
    rw [branchingProduct_eq_prod]
    exact Finset.prod_comm
  simp_rw [hid]
  rw [← branchingMean_eq_expect]
  have hp := branchingMean_pi S T (fun i a y => if V i y=e i a then (1:ℝ) else 0)
  rw [hp]
  exact Finset.prod_congr rfl (fun i _ => (patternMass_eq_branchingMean S (T i) (V i) (e i)).symm)

lemma expect_pi_patterns {n : ℕ} (S : PrescribedTree n) (T : (i : ι) → KernelTower (α i) n)
    (V : (i : ι) → FinitePath (α i) n → Spin) (F : (ι → S.Leaf → Spin) → ℝ) :
    (sampleLaw S (KernelTower.pi n T)).expect
      (fun z => F (fun i a => V i (FinitePath.proj n (pathAt S a z) i))) =
      ∑ e : ι → S.Leaf → Spin, (∏ i, patternMass S (T i) (V i) (e i))*F e := by
  have hid (z : Sample ((i : ι) → α i) S) :
      F (fun i a => V i (FinitePath.proj n (pathAt S a z) i)) =
      ∑ e, (if (fun i a => V i (FinitePath.proj n (pathAt S a z) i))=e then (1:ℝ) else 0)*F e := by
    simp
  calc
    _ = (sampleLaw S (KernelTower.pi n T)).expect (fun z => ∑ e,
      (if (fun i a => V i (FinitePath.proj n (pathAt S a z) i))=e then (1:ℝ) else 0)*F e) :=
      FiniteLaw.expect_congr _ hid
    _ = _ := by simp only [FiniteLaw.expect_fintype_sum,FiniteLaw.expect_mul_right,patternMass_pi]

lemma treeMean_pi_patterns {n : ℕ} (S : PrescribedTree n) (T : (i : ι) → KernelTower (α i) n)
    (V : (i : ι) → FinitePath (α i) n → Spin) (f : (ι → Spin) → ℝ) :
    treeMean S (KernelTower.pi n T) (fun y => f (fun i => V i (FinitePath.proj n y i))) =
      ∑ e : ι → S.Leaf → Spin, (∏ i, patternMass S (T i) (V i) (e i))*(∏ a, f (fun i => e i a)) := by
  rw [treeMean_eq_expect]
  have hh := expect_pi_patterns S T V (fun e => ∏ a, f (fun i => e i a))
  rw [← hh]
  apply FiniteLaw.expect_congr
  intro z
  exact leafProduct_eq_prod S _ z

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootPatternComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree Pattern
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
noncomputable local instance rootPatternComparisonDecidableEq_ra22664_1 (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma root_pattern_replacement (hN : 0<N) (a : ℕ)
    (f : (Fin a → S.Leaf → Spin) → ℝ) (hf : ∀ x, |f x|≤1) :
    |(∫ z, rootTreeMean S T Q m base old
        (fun y => ∑ x, (∏ i, empirical (fun v b => V (y b) v) (x i))*f x) z ∂μ)-
      (∑ x, (∏ i, rootPatternMass μ S T Q m base old V (x i))*f x)| ≤
      (a:ℝ)*shapeDeviation μ
        (rootAlphabet (Ω := Ω) (A := A)) S (rootTower T Q m base old)
        (rootVector (fun y i => spin (V y i))) := by
  let α := rootAlphabet (Ω := Ω) (A := A) (Y := Y) (X := X) (M := M)
  let K := rootTower T Q m base old
  let P := fun z => sampleLaw S (K z)
  let mass := fun z (w : Sample (α z) S) =>
    empirical (fun i b => V (physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b w)) i)
  have hm (e : S.Leaf → Spin) : Measurable (fun z => (P z).expect (fun w => mass z w e)) :=
    measurable_rootTreeMean S T Q m base old (fun x => empirical (fun i b => V (x b) i) e) hb
  have he := mixed_pattern_replacement μ (fun z => Sample (α z) S) P mass
    (fun z w => empirical_nonneg _) (fun z w => empirical_total hN _) hm a f hf
    (measurable_rootTreeMean S T Q m base old
      (fun y => ∑ x, (∏ i, empirical (fun v b => V (y b) v) (x i))*f x) hb)
    (fun B => measurable_rootTreeMean S T Q m base old
      (fun y => |moment (empirical (fun i b => V (y b) i)) B -
        moment (mixedMass μ (fun z => Sample (α z) S) P mass) B|) hb)
  change |(∫ z, (P z).expect (fun w => ∑ x, (∏ i, mass z w (x i))*f x) ∂μ)-
    (∑ x, (∏ i, mixedMass μ (fun z => Sample (α z) S) P mass (x i))*f x)|≤_ 
  apply he.trans_eq
  congr 1
  have hmom (B : Finset S.Leaf) (z : FullRootState Y X I M) (w : Sample (α z) S) :
      moment (mass z w) B = subsetOverlap S B
        (rootVector (fun y i => spin (V y i)) z) w := by
    rw [empirical_moment]
    rfl
  simp_rw [hmom]
  change (∑ B∈(Finset.univ : Finset (Finset S.Leaf)).erase ∅,
    subsetDeviation μ α S B K (rootVector (fun y i => spin (V y i)))) = _
  unfold shapeDeviation
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ∅)]
  have hempty (z : FullRootState Y X I M) :
      subsetOverlap S ∅ (rootVector (fun y i => spin (V y i)) z) = (fun _ : Sample (α z) S => (N:ℝ)/N) := by
    funext w
    simp [subsetOverlap]
  have hz : subsetDeviation μ α S ∅ K (rootVector (fun y i => spin (V y i)))=0 := by
    simp only [subsetDeviation,hempty,FiniteLaw.mixedDeviation,
      FiniteLaw.expect_const,integral_const,probReal_univ,smul_eq_mul,one_mul,sub_self,abs_zero]
  have hh : (∑ B : Finset S.Leaf,
    if B.Nonempty then subsetDeviation μ α S B K (rootVector (fun y i => spin (V y i))) else 0) =
      ∑ B : Finset S.Leaf, subsetDeviation μ α S B K (rootVector (fun y i => spin (V y i))) := by
    apply Finset.sum_congr rfl
    intro B _
    by_cases h : B.Nonempty
    · rw [ite_eq_left h]
    · rw [ite_eq_right h,Finset.not_nonempty_iff_eq_empty.mp h,hz]
  rw [hh,hz,sub_zero]

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace Pattern
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} [NeZero N]

omit [DecidableEq ι] in
lemma empirical_eq_uniform (σ : Fin N → ι → Spin) (e : ι → Spin) :
    empirical σ e = (FiniteLaw.uniform : FiniteLaw (Fin N)).expect
      (fun i => if σ i=e then 1 else 0) := by
  classical
  rw [FiniteLaw.expect_uniform,Fintype.card_fin]
  rfl

lemma uniform_patterns (σ : Fin N → ι → Spin) (a : ℕ)
    (f : (Fin a → ι → Spin) → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (Fin a → Fin N)).expect (fun x => f (fun i => σ (x i))) =
      ∑ e, (∏ i, empirical σ (e i))*f e := by
  classical
  rw [← FiniteLaw.pi_uniform,FiniteLaw.expect_pi_map (fun _ : Fin a => (FiniteLaw.uniform : FiniteLaw (Fin N)))
    (fun _ => σ) f]
  change (∑ e, (∏ i, (FiniteLaw.map FiniteLaw.uniform σ).weight (e i))*f e)=_
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [empirical_eq_uniform]
  dsimp only [FiniteLaw.map]
  apply FiniteLaw.expect_congr
  intro v
  split_ifs <;> rfl

end Pattern

namespace PrescribedTree
variable {Ω : Type} [Fintype Ω] {N n : ℕ} [NeZero N]
lemma treeMean_uniform_patterns (S : PrescribedTree n) (T : KernelTower Ω n)
    (V : FinitePath Ω n → Fin N → Spin) (a : ℕ) (f : (Fin a → Spin) → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (Fin a → Fin N)).expect (fun i =>
      treeMean S T (fun y => f (fun j => V y (i j)))) =
      (sampleLaw S T).expect (fun w => ∑ e : Fin a → S.Leaf → Spin,
        (∏ j, Pattern.empirical (fun i b => V (S.pathAt b w) i) (e j))*(∏ b, f (fun j => e j b))) := by
  simp_rw [treeMean_eq_expect]
  rw [FiniteLaw.expect_comm]
  apply FiniteLaw.expect_congr
  intro w
  simp_rw [leafProduct_eq_prod]
  exact Pattern.uniform_patterns (fun i b => V (S.pathAt b w) i) a (fun e => ∏ b, f (fun j => e j b))

end PrescribedTree
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z]

/-- Comparing two integrated finite expansions only requires finitely many
 coefficient errors, with the same uniform geometric remainder. -/
lemma logExpansion_comparison {A B : ℝ} {a b : ℕ → ℝ} (K : ℕ) {t R : ℝ}
    (hA : |A-∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*a k*t^(k+1)|≤R)
    (hB : |B-∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*b k*t^(k+1)|≤R) :
    |A-B|≤2*R+∑ k∈Finset.range K, |t|^(k+1)/(k+1)*|a k-b k| := by
  let U := ∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*a k*t^(k+1)
  let V := ∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*b k*t^(k+1)
  have hUV : |U-V|≤∑ k∈Finset.range K, |t|^(k+1)/(k+1)*|a k-b k| := by
    dsimp only [U,V]
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k _
    have he : (-1:ℝ)^k/(k+1)*a k*t^(k+1)-(-1:ℝ)^k/(k+1)*b k*t^(k+1)=
        ((-1:ℝ)^k*t^(k+1)/(k+1))*(a k-b k) := by ring
    rw [he,abs_mul,abs_div,abs_mul,abs_pow,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_pos (show (0:ℝ)<k+1 by positivity)]
  have h1 := abs_sub_le A U B
  have h2 := abs_sub_le U V B
  rw [abs_sub_comm V B] at h2
  dsimp only [U,V] at h1 h2 hUV
  linarith

end DilutedSpinGlass.PrescribedTree

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
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n : ℕ}

lemma qExpect_sub (m : Fin (n+1) → ℝ) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T-G T) k S=qExpect m F k S-qExpect m G k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,mul_sub,Finset.sum_sub_distrib]

lemma abs_qExpect_le_qExpect_abs (m : Fin (n+1) → ℝ) (hm : Monotone m)
    (hpos : ∀ j, 0 ≤ m j) (F : PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    |qExpect m F k S| ≤ qExpect m (fun T => |F T|) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    unfold qExpect
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro v _
    have hcoef := div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg S.leaves)
    rw [abs_mul,abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left (ih (grow S v)) hcoef

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

lemma qExpect_difference_bound (m : Fin (n+1) → ℝ) (hm : Monotone m)
    (hpos : ∀ j, 0 ≤ m j) (F G E : PrescribedTree n → ℝ)
    (h : ∀ S, |F S-G S|≤E S) (k : ℕ) (S : PrescribedTree n) :
    |qExpect m F k S-qExpect m G k S|≤qExpect m E k S := by
  rw [← qExpect_sub]
  exact (abs_qExpect_le_qExpect_abs m hm hpos _ k S).trans (qExpect_mono m hm hpos h k S)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter _root_.MeasureTheory
open scoped NNReal Topology

lemma reservoirRate_nonzero (α : ℝ≥0) (hα : 0 < α) (q N : ℕ) (hN : 0 < N) :
    0 < reservoirRate α q N := by
  unfold reservoirRate
  positivity

lemma reservoirRate_le (α : ℝ≥0) (q N : ℕ) : reservoirRate α q N ≤ α*N := by
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).mpr (by simp))

lemma reservoirRate_lower (α : ℝ≥0) (q N : ℕ) :
    (α:ℝ)*((N:ℝ)-q) ≤ reservoirRate α q N := by
  have hden : (0:ℝ) < N+1 := by positivity
  have hx0 : (0:ℝ) ≤ N/(N+1) := by positivity
  have hx1 : (N:ℝ)/(N+1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hb := one_add_mul_sub_le_pow (R := ℝ) (a := (N:ℝ)/(N+1)) (by linarith : -1 ≤ (N:ℝ)/(N+1)) q
  have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ α*N by positivity)
  have he : (N:ℝ)/(N+1)-1 = -1/(N+1) := by field_simp; ring
  rw [he] at hh
  have hqq : (N:ℝ)*q/(N+1) ≤ q := by
    rw [div_le_iff₀ hden]
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  change (α:ℝ)*((N:ℝ)-q) ≤ (α:ℝ)*N*((N:ℝ)/(N+1))^q
  calc
    _ ≤ (α:ℝ)*(N-N*q/(N+1)) := mul_le_mul_of_nonneg_left (by linarith) α.coe_nonneg
    _ = (α:ℝ)*N*(1+q*(-1/(N+1))) := by ring
    _ ≤ _ := hh

lemma reservoirRate_deficit_le (α : ℝ≥0) (q N : ℕ) :
    ((α*N-reservoirRate α q N:ℝ≥0):ℝ) ≤ (α:ℝ)*q := by
  rw [NNReal.coe_sub (reservoirRate_le α q N)]
  push_cast
  linarith [reservoirRate_lower α q N]

lemma reservoirRate_tendsto (α : ℝ≥0) (hα : 0 < α) (q : ℕ) :
    Tendsto (fun N => (reservoirRate α q N:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun N => reservoirRate_lower α q N)
  have hn : Tendsto (fun N : ℕ => (N:ℝ)-(q:ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (-(q:ℝ)) tendsto_natCast_atTop_atTop
  exact hn.const_mul_atTop hα

lemma reservoirDistance_nonneg (α : ℝ≥0) (q N : ℕ) : 0 ≤ reservoirDistance α q N := by
  unfold reservoirDistance
  positivity

lemma reservoirDistance_tendsto (α : ℝ≥0) (hα : 0 < α) (q : ℕ) :
    Tendsto (reservoirDistance α q) atTop (𝓝 0) := by
  have hh := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (reservoirRate_tendsto α hα q))).const_mul ((α:ℝ)*q)
  simp only [mul_zero] at hh
  apply squeeze_zero (reservoirDistance_nonneg α q) _ hh
  intro N
  exact mul_le_mul_of_nonneg_right (reservoirRate_deficit_le α q N) (by positivity)

lemma fullRoot_reservoirDistance {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] {M : ℕ}
    (ξ : Fin M → Measure Y) [∀ i, IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (α s : ℝ≥0) (hα : 0 < α) (q N : ℕ) (hN : 0 < N) :
    BoundedDistance (fullRootLaw ξ μ ν (α*N) s)
      (fullRootLaw ξ μ ν (reservoirRate α q N) s) (reservoirDistance α q N) := by
  have he : reservoirRate α q N+(α*N-reservoirRate α q N)=α*N :=
    add_tsub_cancel_of_le (reservoirRate_le α q N)
  simpa only [he,reservoirDistance] using fullRoot_boundedDistance ξ μ ν
    (reservoirRate α q N) (α*N-reservoirRate α q N) s (reservoirRate_nonzero α hα q N hN)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootDeviationDistance
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable {μ ν : Measure (FullRootState Y X I M)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℝ} (hd : BoundedDistance μ ν d)
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ y i, |V y i| ≤ 1)

include hd hb hV in
lemma root_subsetDeviation_distance (B : Finset S.Leaf) :
    |subsetDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S B
      (rootTower T Q m base old) (rootVector V) -
     subsetDeviation ν (rootAlphabet (Ω := Ω) (A := A)) S B
      (rootTower T Q m base old) (rootVector V)| ≤ 3*d := by
  apply FiniteLaw.mixedDeviation_distance hd
  · intro z w
    exact subsetOverlap_bound S B _ (fun y i => hV _ i) w
  · exact measurable_rootTreeMean S T Q m base old
      (fun x => (∑ i, ∏ a∈B, V (x a) i)/(N:ℝ)) hb
  · intro c
    exact measurable_rootTreeMean S T Q m base old
      (fun x => |(∑ i, ∏ a∈B, V (x a) i)/(N:ℝ)-c|) hb

include hd hb hV in
lemma root_shapeDeviation_distance (hd0 : 0 ≤ d) :
    |shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S
      (rootTower T Q m base old) (rootVector V) -
     shapeDeviation ν (rootAlphabet (Ω := Ω) (A := A)) S
      (rootTower T Q m base old) (rootVector V)| ≤ (2:ℝ)^S.leaves*(3*d) := by
  classical
  unfold shapeDeviation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _B : Finset S.Leaf, 3*d := by
      apply Finset.sum_le_sum
      intro B _
      by_cases hB : B.Nonempty
      · simp only [ite_eq_left hB]
        exact root_subsetDeviation_distance hd S T Q m base old V hb hV B
      · simp only [ite_eq_right hB,sub_self,abs_zero]
        positivity
    _ = _ := by simp [card_leaf]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteTowerPi
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

lemma reservoirShapeDeviation_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    0 ≤ reservoirShapeDeviation M C H N L u S := shapeDeviation_nonneg _ _ _ _ _

lemma reservoirShapeDeviation_distance (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (N L : ℕ) (hN : 0<N) (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    |physicalShapeDeviation M C H N L u S-reservoirShapeDeviation M C H N L u S|≤
      (2:ℝ)^S.leaves*(3*reservoirDistance M.alpha (p-1) N) := by
  apply root_shapeDeviation_distance
    (fullRoot_reservoirDistance _ _ _ _ _ hα (p-1) N hN)
    S _ _ _ _ _ _ (measurable_physicalBase M C H N)
    (fun y i => readVector_bound _ y i) (reservoirDistance_nonneg _ _ _)

lemma reservoirShape_qExpect_distance (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (N L : ℕ) (hN : 0<N) (u : Spec L×ℕ → ℝ) (k : ℕ) :
    |qExpect (grid (L+1) 0 (L+1)) (physicalShapeDeviation M C H N L u) k (single (L+1))-
      qExpect (grid (L+1) 0 (L+1)) (reservoirShapeDeviation M C H N L u) k (single (L+1))|≤
      (2:ℝ)^(k+1)*(3*reservoirDistance M.alpha (p-1) N) := by
  have hh := qExpect_difference_bound (grid (L+1) 0 (L+1))
    (grid_strictMono (by omega)).monotone grid_nonneg _ _ _
    (reservoirShapeDeviation_distance M hα C H N L hN u) k (single (L+1))
  apply hh.trans
  have h := qExpect_mono_leaves (grid (L+1) 0 (L+1))
    (grid_strictMono (by omega)).monotone grid_nonneg
    (fun S => (2:ℝ)^S.leaves*(3*reservoirDistance M.alpha (p-1) N))
    (fun _ => (2:ℝ)^(k+1)*(3*reservoirDistance M.alpha (p-1) N)) k (single (L+1))
    (fun S hS => by rw [hS,leaves_single,Nat.add_comm 1 k])
  have hz : grid (L+1) 0 (L+1) 0=0 := by simp [grid]
  simpa only [qExpect_const _ hz (grid_last (by omega : 0<L+1))] using h

lemma reservoirShape_qExpect_difference_tendsto (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (L : ℕ) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (us : ℕ → Spec L×ℕ → ℝ)
    (k : ℕ) :
    Tendsto (fun n => qExpect (grid (L+1) 0 (L+1))
      (physicalShapeDeviation M C H (Ns n+1) L (us n)) k (single (L+1))-
      qExpect (grid (L+1) 0 (L+1))
      (reservoirShapeDeviation M C H (Ns n+1) L (us n)) k (single (L+1))) atTop (𝓝 0) := by
  have hd := (reservoirDistance_tendsto M.alpha hα (p-1)).comp
    (tendsto_add_atTop_nat 1 |>.comp hNs)
  have hh := (hd.const_mul 3).const_mul ((2:ℝ)^(k+1))
  simp only [mul_zero,Function.comp_apply] at hh
  exact squeeze_zero_norm (fun n : ℕ => by simpa only [Real.norm_eq_abs] using
      (reservoirShape_qExpect_distance M hα C H (Ns n+1) L (by omega) (us n) k)) hh

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirShapeLimit
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
lemma reservoirShapeDeviation_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    reservoirShapeDeviation M C H N L u S ≤ (2:ℝ)^S.leaves*2 := by
  unfold reservoirShapeDeviation
  exact shapeDeviation_bound _ _ _ _ _ (fun z y i => readVector_bound _ _ _)
lemma physicalShapeDeviation_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    physicalShapeDeviation M C H N L u S ≤ (2:ℝ)^S.leaves*2 := by
  unfold physicalShapeDeviation
  exact shapeDeviation_bound _ _ _ _ _ (fun z y i => readVector_bound _ _ _)

lemma reservoirShapeError_tendsto (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L, Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))) atTop)
      atTop (𝓝 0) := by
  let f := fun L n => qExpect (grid (L+1) 0 (L+1))
    (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  let g := fun L n => qExpect (grid (L+1) 0 (L+1))
    (physicalShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  have hf (L n : ℕ) : 0≤f L n := qExpect_nonneg _
    (grid_strictMono (by omega)).monotone grid_nonneg _
    (reservoirShapeDeviation_nonneg _ _ _ _ _ _) _ _
  have hfb (L : ℕ) : IsBoundedUnder (·≤·) atTop (f L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact reservoirShapeDeviation_bound _ _ _ _ _ _ _
  have hgb (L : ℕ) : IsBoundedUnder (·≤·) atTop (g L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact physicalShapeDeviation_bound _ _ _ _ _ _ _
  apply squeeze_zero (fun L => le_limsup_of_frequently_le ((Eventually.of_forall (hf L)).frequently) (hfb L)) _
    (physicalShapeError_tendsto M C H Ns us hcontrol k)
  intro L
  exact limsup_le_of_vanishing_error (f L) (g L) (fun n => -(g L n-f L n)) (hf L) (hgb L)
    (by simpa only [neg_zero] using
      (reservoirShape_qExpect_difference_tendsto M hα C H L (Ns L) (hNs L) (us L) k).neg)
    (fun n => by linarith)
end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FunctionalStability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.HeterogeneousMarks.functionalStabilityRootMeasurableSpace
local instance functionalStabilityRootBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
lemma integral_independentInsertion_trialLog (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (hm : ∀ i, 0 < m i) (hend : m (Fin.last L)=1)
    (hV : ∀ z i, TerminalInterior L (rootTower T Q m base old z)
      (fun y => rootVector (fun w j => spin (V w j)) z y i)) :
    (∫ z, independentInsertion T Q m base old V a F z
      ∂Measure.pi (fun _ : Fin a => μ.prod (siteLaw N))) =
      trialLog L (rootEncodingLaw T Q m base old (fun w j => spin (V w j)) hb μ)
        (fun i => m i.castSucc) (FiniteLaw.spinLog F) := by
  let enc := fun z : FullRootState Y X I M × Site N =>
    rootEncoding T Q m base old (fun w j => spin (V w j)) z.1 z.2
  have he : Measurable enc := measurable_rootEncoding_joint T Q m base old _ hb
  have hf : ∀ s, |F s|≤∑ t, |F t| := fun s =>
    Finset.single_le_sum (fun t _ => abs_nonneg (F t)) (Finset.mem_univ s)
  have hc := (logMean_continuous_bound L _ (FiniteLaw.spinLog_continuous F)
    (FiniteLaw.spinLog_bound F hf) (fun i => m i.castSucc) (fun i => hm i.castSucc)).1
  change _ = ∫ η, logMean L (FiniteLaw.spinLog F) (fun i => m i.castSucc) η
    ∂Measure.pi (fun _ : Fin a => Measure.map enc (μ.prod (siteLaw N)))
  have hme : Measurable (fun z : Fin a → FullRootState Y X I M × Site N => fun i => enc (z i)) :=
    Measurable.of_eval (fun index => he.comp (measurable_pi_apply index))
  rw [← Measure.pi_map_pi (fun _ : Fin a => he.aemeasurable)]
  rw [integral_map hme.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  exact independentInsertion_encode T Q m base old V a F hend hV z
end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootPatternProduct
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree Pattern ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootSitePattern (e : S.Leaf → Spin) :
    Measurable (rootSitePattern S T Q m base old V e) := by
  unfold rootSitePattern
  apply measurable_from_prod_countable_left
  intro i
  exact measurable_rootTreeMean S T Q m base old
    (fun y : S.Leaf → FinitePath Ω L => if (fun a => V (y a) i)=e then 1 else 0) hb

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootSitePattern_bound (e : S.Leaf → Spin) (z : FullRootState Y X I M × Site N) :
    |rootSitePattern S T Q m base old V e z|≤1 :=
  rootTreeMean_bound S T Q m base old _ (fun y => by split_ifs <;> norm_num) z.1

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootSitePattern_eq (e : S.Leaf → Spin) (z : FullRootState Y X I M × Site N) :
    rootSitePattern S T Q m base old V e z =
      patternMass S (rootTower T Q m base old z.1)
        (fun y => V (physical (rootArray z.1.2.2.1 z.1.2.2.2) L y) z.2) e := by
  apply FiniteLaw.expect_congr
  intro w
  dsimp only

include hb in
lemma integral_rootSitePattern (e : S.Leaf → Spin) :
    (∫ z, rootSitePattern S T Q m base old V e z ∂μ.prod (siteLaw N)) =
      rootPatternMass μ S T Q m base old V e := by
  have hi : Integrable (rootSitePattern S T Q m base old V e) (μ.prod (siteLaw N)) :=
    (bounded_memLp (measurable_rootSitePattern S T Q m base old V hb e)
      (rootSitePattern_bound S T Q m base old V e) 1).integrable le_rfl
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_siteLaw]
  change (∑ i : Site N, (sampleLaw S (rootTower T Q m base old z)).expect
    (fun w => if (fun a => V (physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt a w)) i)=e then 1 else 0)) / (max N 1:ℕ) = _
  rw [← FiniteLaw.expect_fintype_sum,← FiniteLaw.expect_div]
  apply FiniteLaw.expect_congr
  intro w
  rfl

include hb in
lemma integral_independent_patterns (a : ℕ) (f : (Fin a → S.Leaf → Spin) → ℝ) :
    (∫ z : Fin a → FullRootState Y X I M × Site N,
      ∑ e : Fin a → S.Leaf → Spin,
        (∏ i, rootSitePattern S T Q m base old V (e i) (z i))*f e
      ∂Measure.pi (fun _ : Fin a => μ.prod (siteLaw N))) =
      ∑ e, (∏ i, rootPatternMass μ S T Q m base old V (e i))*f e := by
  have hip (e : Fin a → S.Leaf → Spin) : Integrable
      (fun z : Fin a → FullRootState Y X I M × Site N =>
        ∏ i, rootSitePattern S T Q m base old V (e i) (z i))
      (Measure.pi (fun _ : Fin a => μ.prod (siteLaw N))) := by
    apply (bounded_memLp (Finset.measurable_fun_prod _ (fun i _ =>
      (measurable_rootSitePattern S T Q m base old V hb (e i)).comp (measurable_pi_apply i)))
      (B := 1) ?_ 1).integrable le_rfl
    intro z
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => rootSitePattern_bound S T Q m base old V (e i) (z i))
  rw [integral_finsetSum _ (fun e _ => (hip e).mul_const _)]
  simp only [integral_mul_const]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl (fun i _ => integral_rootSitePattern μ S T Q m base old V hb (e i))

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootCoefficients
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree Pattern ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameTreeCoefficient_patterns (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) :
    sameTreeCoefficient S T Q m base old V a f z =
      rootTreeMean S T Q m base old (fun y => ∑ e : Fin a → S.Leaf → Spin,
        (∏ j, empirical (fun i b => V (y b) i) (e j))*(∏ b, f (fun j => e j b))) z := by
  unfold sameTreeCoefficient
  rw [treeMean_uniform_patterns]
  rfl

include hb in
lemma measurable_sameTreeCoefficient (a : ℕ) (f : (Fin a → Spin) → ℝ) :
    Measurable (sameTreeCoefficient S T Q m base old V a f) := by
  simp_rw [show sameTreeCoefficient S T Q m base old V a f = fun z =>
      rootTreeMean S T Q m base old (fun y => ∑ e : Fin a → S.Leaf → Spin,
        (∏ j, empirical (fun i b => V (y b) i) (e j))*(∏ b, f (fun j => e j b))) z from
    funext (sameTreeCoefficient_patterns S T Q m base old V a f)]
  exact measurable_rootTreeMean S T Q m base old _ hb

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameTreeCoefficient_bound (a : ℕ) (f : (Fin a → Spin) → ℝ) (hf : ∀ s, |f s|≤1)
    (z : FullRootState Y X I M) : |sameTreeCoefficient S T Q m base old V a f z|≤1 := by
  apply FiniteLaw.abs_expect_le
  intro i
  exact treeMean_bound S _ (fun y => hf _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentTreeCoefficient_patterns (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (z : Fin a → FullRootState Y X I M × Site N) :
    independentTreeCoefficient S T Q m base old V a f z =
      ∑ e : Fin a → S.Leaf → Spin,
        (∏ i, rootSitePattern S T Q m base old V (e i) (z i))*(∏ b, f (fun j => e j b)) := by
  unfold independentTreeCoefficient
  have hh := treeMean_pi_patterns (α := fun i : Fin a => rootAlphabet (Ω := Ω) (A := A) (z i).1)
    S (fun i => rootTower T Q m base old (z i).1)
    (fun i y => V (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) L y) (z i).2) f
  simpa only [rootSitePattern_eq] using hh

include hb in
lemma measurable_independentTreeCoefficient (a : ℕ) (f : (Fin a → Spin) → ℝ) :
    Measurable (independentTreeCoefficient S T Q m base old V a f) := by
  simp_rw [show independentTreeCoefficient S T Q m base old V a f = fun z =>
      ∑ e : Fin a → S.Leaf → Spin,
        (∏ i, rootSitePattern S T Q m base old V (e i) (z i))*(∏ b, f (fun j => e j b)) from
    funext (independentTreeCoefficient_patterns S T Q m base old V a f)]
  apply Finset.measurable_fun_sum
  intro e _
  apply Measurable.mul_const
  exact Finset.measurable_fun_prod _ (fun i _ =>
    (measurable_rootSitePattern S T Q m base old V hb (e i)).comp (measurable_pi_apply i))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentTreeCoefficient_bound (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (hf : ∀ s, |f s|≤1) (z : Fin a → FullRootState Y X I M × Site N) :
    |independentTreeCoefficient S T Q m base old V a f z|≤1 :=
  treeMean_bound S _ (fun _ => hf _)

include hb in
lemma integral_treeCoefficient_comparison (a : ℕ) (f : (Fin a → Spin) → ℝ) (hf : ∀ s, |f s|≤1) :
    |(∫ z, sameTreeCoefficient S T Q m base old V a f z ∂μ)-
      (∫ z, independentTreeCoefficient S T Q m base old V a f z
        ∂Measure.pi (fun _ : Fin a => μ.prod (siteLaw N)))| ≤
      (a:ℝ)*shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S (rootTower T Q m base old)
        (rootVector (fun y i => spin (V y i))) := by
  simp_rw [sameTreeCoefficient_patterns,independentTreeCoefficient_patterns]
  rw [integral_independent_patterns μ S T Q m base old V hb]
  apply root_pattern_replacement μ S T Q m base old V hb (by omega) a
  intro e
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)
end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators
namespace PrescribedTree
variable {β : Type} [Fintype β] {n : ℕ}
lemma expect_qExpect (P : FiniteLaw β) (m : Fin (n+1) → ℝ)
    (F : β → PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    P.expect (fun z => qExpect m (F z) k S) = qExpect m (fun T => P.expect (fun z => F z T)) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect, FiniteLaw.expect_fintype_sum, FiniteLaw.expect_mul_left, ih]

lemma normalized_backwardLog_tail {Ω : Type} [Fintype Ω] (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (F : FinitePath Ω n → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ y, |F y|≤C) (K : ℕ) :
    |(KernelTower.backwardLog n T (fun i => m i.succ) F-C)-∑ k∈Finset.range K,
      (-1:ℝ)^k/(k+1)*qMoment m T (fun y => normalizedInsertion C (F y)) k (single n)*
        insertionRadius C^(k+1)|≤∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
  rw [KernelTower.backwardLog_normalized T m hnz F hC,add_sub_cancel_right]
  exact logInsertion_tail_bound T m hm hpos hnz hroot hend _
    (fun y => normalizedInsertion_bound hC (hF y))
    (by rw [abs_of_pos (insertionRadius_pos hC)]; exact insertionRadius_lt_one _) K
end PrescribedTree

lemma integral_expansion_tail {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (A : Z → ℝ) (a : Z → ℕ → ℝ) (K : ℕ) (c : ℕ → ℝ) {C R : ℝ}
    (hA : Integrable A μ) (ha : ∀ k, Integrable (fun z => a z k) μ)
    (h : ∀ z, |(A z-C)-∑ k∈Finset.range K,c k*a z k|≤R) :
    |((∫ z, A z ∂μ)-C)-∑ k∈Finset.range K,c k*(∫ z, a z k ∂μ)|≤R := by
  have he : (∑ k∈Finset.range K,c k*(∫ z, a z k ∂μ)) =
      ∫ z, ∑ k∈Finset.range K,c k*a z k ∂μ := by
    rw [integral_finsetSum _ (fun k _ => (ha k).const_mul _)]
    simp only [integral_const_mul]
  have hai : Integrable (fun z => A z-C) μ := hA.sub (integrable_const C)
  have hbi : Integrable (fun z => ∑ k∈Finset.range K,c k*a z k) μ :=
    integrable_finsetSum _ (fun k _ => (ha k).const_mul (c k))
  have hc : (∫ _z : Z, C ∂μ)=C := by simp
  rw [he,← hc,← integral_sub hA (integrable_const C),
    ← integral_sub hai hbi]
  exact abs_integral_le_bound h
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SameInsertionAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_sameInsertionAverage (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    Measurable (sameInsertionAverage T Q m base old V a F) := by
  unfold sameInsertionAverage FiniteLaw.expect
  exact Finset.measurable_fun_sum _ (fun i _ =>
    ((measurable_rootInsertion T Q m base old V hb a F).comp
      (measurable_id.prodMk measurable_const)).const_mul _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameInsertionAverage_bound (hm : ∀ i, 0 < m i) (a : ℕ)
    (F : (Fin a → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C) (z : FullRootState Y X I M) :
    |sameInsertionAverage T Q m base old V a F z|≤C := by
  apply FiniteLaw.abs_expect_le
  intro i
  exact backwardLog_bound (L+1) _ m hm (fun y => hF _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentInsertion_bound (hm : ∀ i, 0 < m i) (a : ℕ)
    (F : (Fin a → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C)
    (z : Fin a → FullRootState Y X I M × Site N) :
    |independentInsertion T Q m base old V a F z|≤C :=
  backwardLog_bound (L+1) _ m hm (fun _ => hF _)

variable (q : Fin (L+2) → ℝ)
omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma same_qMoment (a : ℕ) (f : (Fin a → Spin) → ℝ) (k : ℕ) (S : PrescribedTree (L+1))
    (z : FullRootState Y X I M) :
    (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
      qMoment q (rootTower T Q m base old z)
        (fun y => f (fun j => V (physical (rootArray z.2.2.1 z.2.2.2) (L+1) y) (i j))) k S) =
      qExpect q (fun R => sameTreeCoefficient R T Q m base old V a f z) k S := by
  simp only [qMoment, ← treeMean_eq_expect]
  rw [expect_qExpect]
  rfl

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameInsertionAverage_tail (hm : Monotone q) (hpos : ∀ j, 0 ≤ q j)
    (hnz : ∀ j : Fin (L+1), q j.succ≠0) (hroot : q 0=0) (hend : q (Fin.last (L+1))=1)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ s, |F s|≤C)
    (z : FullRootState Y X I M) (K : ℕ) :
    |(sameInsertionAverage T Q (fun i => q i.succ) base old V a F z-C)-
      ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*
        qExpect q (fun R => sameTreeCoefficient R T Q (fun i => q i.succ) base old V a
          (fun s => normalizedInsertion C (F s)) z) k (single (L+1))*insertionRadius C^(k+1)| ≤
      ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
  have hh := (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).abs_expect_le (fun i =>
    normalized_backwardLog_tail (rootTower T Q (fun j => q j.succ) base old z)
      q hm hpos hnz hroot hend
      (fun y => F (fun j => V (physical (rootArray z.2.2.1 z.2.2.2) (L+1) y) (i j)))
      hC (fun y => hF _) K)
  simp only [FiniteLaw.expect_sub,FiniteLaw.expect_const,FiniteLaw.expect_sum,
    FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_right] at hh
  change |(sameInsertionAverage T Q (fun i => q i.succ) base old V a F z-C)-
    ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*
      (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
        qMoment q (rootTower T Q (fun j => q j.succ) base old z)
          (fun y => normalizedInsertion C (F (fun j =>
            V (physical (rootArray z.2.2.1 z.2.2.2) (L+1) y) (i j)))) k (single (L+1)))*
        insertionRadius C^(k+1)| ≤ _ at hh
  simp_rw [same_qMoment T Q (fun i => q i.succ) base old V q a
    (fun s => normalizedInsertion C (F s))] at hh
  exact hh

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentInsertion_tail (hm : Monotone q) (hpos : ∀ j, 0 ≤ q j)
    (hnz : ∀ j : Fin (L+1), q j.succ≠0) (hroot : q 0=0) (hend : q (Fin.last (L+1))=1)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ s, |F s|≤C)
    (z : Fin a → FullRootState Y X I M × Site N) (K : ℕ) :
    |(independentInsertion T Q (fun i => q i.succ) base old V a F z-C)-
      ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*
        qExpect q (fun R => independentTreeCoefficient R T Q (fun i => q i.succ) base old V a
          (fun s => normalizedInsertion C (F s)) z) k (single (L+1))*insertionRadius C^(k+1)| ≤
      ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
  have hh := normalized_backwardLog_tail
    (KernelTower.pi (L+1) (fun i : Fin a => rootTower T Q (fun j => q j.succ) base old (z i).1))
    q hm hpos hnz hroot hend
    (fun y => F (fun i => V
      (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) (L+1) (FinitePath.proj (L+1) y i)) (z i).2))
    hC (fun y => hF _) K
  simpa only [qMoment,← treeMean_eq_expect, independentInsertion,
    independentTreeCoefficient] using hh
end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootLogComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (q : Fin (L+2) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
/-- The actual finite-root logarithmic comparison, with an explicit uniform
 geometric remainder and the Q-averaged physical shape defect. -/
lemma integral_root_log_comparison (hm : Monotone q) (hpos : ∀ j, 0 ≤ q j)
    (hnz : ∀ j : Fin (L+1), q j.succ≠0) (hroot : q 0=0) (hend : q (Fin.last (L+1))=1)
    (hV : ∀ z i, TerminalInterior L (rootTower T Q (fun j => q j.succ) base old z)
      (fun y => rootVector (fun w j => spin (V w j)) z y i))
    (a : ℕ) (F : (Fin a → Spin) → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ s, |F s|≤C) (K : ℕ) :
    |(∫ z, sameInsertionAverage T Q (fun j => q j.succ) base old V a F z ∂μ)-
      (∫ z, independentInsertion T Q (fun j => q j.succ) base old V a F z
        ∂Measure.pi (fun _ : Fin a => μ.prod (siteLaw N)))| ≤
      2*(∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1))+
      ∑ k∈Finset.range K, |insertionRadius C|^(k+1)/(k+1)*((a:ℝ)*
        qExpect q (fun S => shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S
          (rootTower T Q (fun j => q j.succ) base old)
          (rootVector (fun y i => spin (V y i)))) k (single (L+1))) := by
  let m := fun i : Fin (L+1) => q i.succ
  let f := fun s => normalizedInsertion C (F s)
  let ν := Measure.pi (fun _ : Fin a => μ.prod (siteLaw N))
  have hmp : ∀ i, 0 < m i := fun i => lt_of_le_of_ne (hpos i.succ) (hnz i).symm
  have hme : m (Fin.last L)=1 := hend
  have hf : ∀ s, |f s|≤1 := fun s => normalizedInsertion_bound hC (hF s)
  let u := fun z k => qExpect q (fun S => sameTreeCoefficient S T Q m base old V a f z) k (single (L+1))
  let v := fun z k => qExpect q (fun S => independentTreeCoefficient S T Q m base old V a f z) k (single (L+1))
  have hui (S : PrescribedTree (L+1)) : Integrable (sameTreeCoefficient S T Q m base old V a f) μ :=
    Pattern.bounded_integrable (measurable_sameTreeCoefficient S T Q m base old V hb a f)
      (sameTreeCoefficient_bound S T Q m base old V a f hf)
  have hvi (S : PrescribedTree (L+1)) : Integrable (independentTreeCoefficient S T Q m base old V a f) ν :=
    Pattern.bounded_integrable (measurable_independentTreeCoefficient S T Q m base old V hb a f)
      (independentTreeCoefficient_bound S T Q m base old V a f hf)
  have hu (k : ℕ) : Integrable (fun z => u z k) μ :=
    integrable_qExpect μ q _ hui k _
  have hv (k : ℕ) : Integrable (fun z => v z k) ν :=
    integrable_qExpect ν q _ hvi k _
  have hAi : Integrable (sameInsertionAverage T Q m base old V a F) μ :=
    Pattern.bounded_integrable (measurable_sameInsertionAverage T Q m base old V hb a F)
      (sameInsertionAverage_bound T Q m base old V hmp a F hF)
  have hBi : Integrable (independentInsertion T Q m base old V a F) ν :=
    Pattern.bounded_integrable (measurable_independentInsertion T Q m base old V hb a F hmp hme hV)
      (independentInsertion_bound T Q m base old V hmp a F hF)
  have hAt := integral_expansion_tail μ _ u K
    (fun k => (-1:ℝ)^k/(k+1)*insertionRadius C^(k+1)) hAi hu
    (fun z => by
      simpa only [u,m,f,mul_assoc,mul_left_comm,mul_comm] using
        sameInsertionAverage_tail T Q base old V q hm hpos hnz hroot hend a F hC hF z K)
  have hBt := integral_expansion_tail ν _ v K
    (fun k => (-1:ℝ)^k/(k+1)*insertionRadius C^(k+1)) hBi hv
    (fun z => by
      simpa only [v,m,f,mul_assoc,mul_left_comm,mul_comm] using
        independentInsertion_tail T Q base old V q hm hpos hnz hroot hend a F hC hF z K)
  have hAt' : |((∫ z, sameInsertionAverage T Q m base old V a F z ∂μ)-C)-
      ∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*(∫ z, u z k ∂μ)*insertionRadius C^(k+1)| ≤
        ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hAt
  have hBt' : |((∫ z, independentInsertion T Q m base old V a F z ∂ν)-C)-
      ∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*(∫ z, v z k ∂ν)*insertionRadius C^(k+1)| ≤
        ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hBt
  have hc (k : ℕ) : |(∫ z, u z k ∂μ)-(∫ z, v z k ∂ν)| ≤ (a:ℝ)*
      qExpect q (fun S => shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S
        (rootTower T Q m base old) (rootVector (fun y i => spin (V y i)))) k (single (L+1)) := by
    dsimp only [u,v]
    rw [integral_qExpect μ q _ hui,integral_qExpect ν q _ hvi]
    have hh := qExpect_difference_bound q hm hpos _ _ _
      (fun S => integral_treeCoefficient_comparison μ S T Q m base old V hb a f hf) k (single (L+1))
    simpa only [mul_comm (a:ℝ),qExpect_mul_const] using hh
  have hh := logExpansion_comparison K hAt' hBt'
  simp only [sub_sub_sub_cancel_right] at hh
  apply hh.trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (hc k) (by positivity)
end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalInsertionComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators Topology
variable {p : ℕ}

lemma grid_succ_eq (L : ℕ) : (fun j : Fin (L+1) => grid (L+1) 0 (L+1) j.succ) = gridExponents L := by
  funext j
  have hh := congr_fun (gridExponents_cons L) j.succ
  simpa only [Fin.cons_succ] using hh.symm

lemma reservoirInsertion_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ} (hF : ∀ s, |F s|≤D) :
    |reservoirInsertion M C H N L u a F|≤D := by
  apply abs_integral_le_bound
  intro z
  exact sameInsertionAverage_bound _ _ _ _ _ _ (gridExponents_pos L) a F hF z

 
lemma reservoirInsertion_comparison (M : Model p) (C H : ℝ) (N L : ℕ) (hN : 0<N)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ}
    (hD : 0≤D) (hF : ∀ s, |F s|≤D) (K : ℕ) :
    |reservoirInsertion M C H N L u a F-
      trialLog L (reservoirTrialLaw M C H N L u)
        (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F)| ≤
      2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1))+
      ∑ k∈Finset.range K, |insertionRadius D|^(k+1)/(k+1)*((a:ℝ)*
        qExpect (grid (L+1) 0 (L+1)) (reservoirShapeDeviation M C H N L u) k (single (L+1))) := by
  let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
  let Q := fun i : Labels L (Site N) => prior i.1.1
  let base := physicalBase (L := L) M C H N
  let old := dictionaryFactor (observableAt direction N) (observableAt anchor N) u
  have hV := terminalInterior_rootTower hN Q (gridExponents L) base old
  have htrial := integral_independentInsertion_trialLog (reservoirLaw M N L) T Q
    (gridExponents L) base old (physicalSpin N L) (measurable_physicalBase M C H N) a F
    (gridExponents_pos L) (gridExponents_last L) hV
  change |reservoirInsertion M C H N L u a F - _|≤_
  rw [show trialLog L (reservoirTrialLaw M C H N L u)
      (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F) = _ from htrial.symm]
  have hqpos (j : Fin (L+1)) : grid (L+1) 0 (L+1) j.succ≠0 := by
    have h := congr_fun (grid_succ_eq L) j
    rw [h]
    exact ne_of_gt (gridExponents_pos L j)
  have hv' : ∀ z i, TerminalInterior L (rootTower T Q
      (fun j => grid (L+1) 0 (L+1) j.succ) base old z)
      (fun y => rootVector (fun w j => spin (physicalSpin N L w j)) z y i) := by
    rw [grid_succ_eq]
    exact hV
  have hh := integral_root_log_comparison (reservoirLaw M N L) T Q
    (grid (L+1) 0 (L+1)) base old (physicalSpin N L) (measurable_physicalBase M C H N)
    (grid_strictMono (by omega)).monotone grid_nonneg hqpos
    (by simp [grid]) (grid_last (by omega)) hv' a F hD hF K
  simp only [grid_succ_eq] at hh
  exact hh
end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalInsertionLimit
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open Filter
open scoped Topology BigOperators
variable {p : ℕ}

lemma logSeries_tail_tendsto (D : ℝ) :
    Tendsto (fun K : ℕ => 2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1))) atTop (𝓝 0) := by
  have hh := (tendsto_sum_nat_add (fun k : ℕ => |insertionRadius D|^(k+1)/((k:ℝ)+1))).const_mul 2
  simpa only [Nat.cast_add,mul_zero] using hh

lemma reservoirTrialLog_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ} (hF : ∀ s, |F s|≤D) :
    |trialLog L (reservoirTrialLaw M C H N L u)
      (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F)|≤D := by
  exact (trialLog_continuous_bound L _ (FiniteLaw.spinLog_continuous F) (FiniteLaw.spinLog_bound F hF)
    _ (fun i => gridExponents_pos L i.castSucc)).2 _

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionStability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι : Type} [Fintype ι]
lemma spinLog_stability (F G : (ι → Spin) → ℝ) {D : ℝ}
    (h : ∀ s, |F s-G s|≤D) (x : ι → ℝ) : |spinLog F x-spinLog G x|≤D := by
  classical
  apply weighted_log_exp_stability _ _ _ (fun s => (Finset.prod_pos (fun i _ => q_pos _ _)).le) _ h
  rw [← Fintype.prod_sum]
  simp only [q_sum,Finset.prod_const_one]
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped BigOperators
variable {p : ℕ}
lemma reservoirInsertion_lipschitz (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) : LipschitzWith 1 (reservoirInsertion M C H N L u a) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  have hi (F : (Fin a → Spin) → ℝ) : Integrable
      (sameInsertionAverage (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
        (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M C H N)
        (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
        (physicalSpin N L) a F) (reservoirLaw M N L) := by
    apply MeasureMean.bounded_integrable
    · exact measurable_sameInsertionAverage _ _ _ _ _ _ (measurable_physicalBase M C H N) a F
    · intro z
      exact sameInsertionAverage_bound _ _ _ _ _ _ (gridExponents_pos L) a F
        (fun s => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm F s) z
  unfold reservoirInsertion
  rw [← integral_sub (hi F) (hi G)]
  apply abs_integral_le_bound
  intro z
  unfold sameInsertionAverage
  rw [← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le
  intro i
  apply backwardLog_stability _ _ _ (gridExponents_pos L)
  intro y
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (F-G) _

lemma reservoirTrialLog_lipschitz (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) : LipschitzWith 1 (fun F : (Fin a → Spin) → ℝ =>
      trialLog L (reservoirTrialLaw M C H N L u)
        (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F)) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  apply trialLog_stability L _ _ (FiniteLaw.spinLog_continuous F) (FiniteLaw.spinLog_continuous G)
    (FiniteLaw.spinLog_bound F (fun s => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm F s))
    (FiniteLaw.spinLog_bound G (fun s => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm G s))
    (fun x => FiniteLaw.spinLog_stability F G (fun s => by
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (F-G) s) x)
    _ (fun i => gridExponents_pos L i.castSucc)
end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RandomInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open Filter
open scoped Topology BigOperators
variable {p : ℕ} {X : Type} [MeasurableSpace X]

lemma randomInsertion_comparison (M : Model p) (C H : ℝ) (N L : ℕ) (hN : 0<N)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → (Fin a → Spin) → ℝ) (hFm : Measurable F) {D : ℝ}
    (hD : 0≤D) (hF : ∀ x s, |F x s|≤D) (K : ℕ) :
    |(∫ x, reservoirInsertion M C H N L u a (F x) ∂μ)-
      (∫ x, trialLog L (reservoirTrialLaw M C H N L u)
        (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ)| ≤
      2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1))+
      ∑ k∈Finset.range K, |insertionRadius D|^(k+1)/(k+1)*((a:ℝ)*
        qExpect (grid (L+1) 0 (L+1)) (reservoirShapeDeviation M C H N L u) k (single (L+1))) := by
  have hi := MeasureMean.bounded_integrable μ
    ((reservoirInsertion_lipschitz M C H N L u a).continuous.measurable.comp hFm)
    (fun x => reservoirInsertion_bound M C H N L u a (F x) (hF x))
  have hj := MeasureMean.bounded_integrable μ
    ((reservoirTrialLog_lipschitz M C H N L u a).continuous.measurable.comp hFm)
    (fun x => reservoirTrialLog_bound M C H N L u a (F x) (hF x))
  simp only [Function.comp_def] at hi hj
  rw [← integral_sub hi hj]
  exact abs_integral_le_bound (μ := μ) (fun x => reservoirInsertion_comparison M C H N L hN u a (F x) hD (hF x) K)

/-- The bounded-insertion limit is uniform in independent physical disorder;
 the physical law is integrated without exchanging the two ordered limits. -/
theorem randomInsertion_comparison_tendsto (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L, Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L))
    (a : ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → (Fin a → Spin) → ℝ) (hFm : Measurable F) {D : ℝ}
    (hD : 0≤D) (hF : ∀ x s, |F x s|≤D) :
    Tendsto (fun L => limsup (fun n =>
      |(∫ x, reservoirInsertion M C H (Ns L n+1) L (us L n) a (F x) ∂μ)-
        (∫ x, trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ)|) atTop) atTop (𝓝 0) := by
  let f := fun k L n => qExpect (grid (L+1) 0 (L+1))
    (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  have hf (k L : ℕ) : IsBoundedUnder (·≤·) atTop (f k L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact reservoirShapeDeviation_bound _ _ _ _ _ _ _
  apply series_double_limit _ f (fun k => |insertionRadius D|^(k+1)/(k+1)*(a:ℝ))
    (fun K => 2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1)))
  · intros; exact abs_nonneg _
  · intro L
    refine isBoundedUnder_of_eventually_le (a := 2*D) (Eventually.of_forall (fun n => ?_))
    have h1 := abs_integral_le_bound (μ := μ) (fun x => reservoirInsertion_bound M C H (Ns L n+1) L (us L n) a (F x) (hF x))
    have h2 := abs_integral_le_bound (μ := μ) (fun x => reservoirTrialLog_bound M C H (Ns L n+1) L (us L n) a (F x) (hF x))
    exact (abs_sub _ _).trans (by linarith)
  · intro k; positivity
  · exact hf
  · exact reservoirShapeError_tendsto M hα C H Ns hNs us hcontrol
  · exact logSeries_tail_tendsto D
  · intro K L n
    simpa only [f,mul_assoc] using randomInsertion_comparison M C H (Ns L n+1) L
      (by omega) (us L n) a μ F hFm hD hF K
end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRootCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal

lemma summable_measure_real_mul {X : Type} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable X] (μ : Measure X) {f : X → ℝ} (hf : Integrable f μ) :
    Summable (fun x => μ.real {x} * f x) := by
  rw [← Measure.sum_smul_dirac μ] at hf
  have he := (hasSum_integral_measure hf).summable
  simpa only [integral_smul_measure,integral_dirac,ENNReal.smul_def,smul_eq_mul,measureReal_def] using he

lemma poisson_mixture_double_limit (r : ℝ≥0) (f : ℕ → ℕ → ℕ → ℝ)
    {B C : ℝ} (hf : ∀ k L n,0≤f k L n) (hb : ∀ k L n,f k L n≤B+C*k)
    (hlim : ∀ k,Tendsto (fun L => limsup (f k L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (fun n => ∫ k,f k L n ∂poissonMeasure r) atTop) atTop (𝓝 0) := by
  have hi (L n : ℕ) : Integrable (fun k => f k L n) (poissonMeasure r) :=
    poisson_integrable_linear r (fun k => by rw [abs_of_nonneg (hf k L n)]; exact hb k L n)
  have he (L n : ℕ) : (∫ k,f k L n ∂poissonMeasure r)=
      ∑' k,(poissonMeasure r).real {k}*f k L n := by
    simpa only [smul_eq_mul] using integral_countable (hi L n)
  simp_rw [he]
  exact mixture_double_limit f (fun k => (poissonMeasure r).real {k}) (fun k => B+C*k)
    (fun _ => measureReal_nonneg) hf hb
    (summable_measure_real_mul _ ((integrable_const B).add ((poisson_integrable_count r).const_mul C))) hlim

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityInsertionAlgebra
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
open _root_.MeasureTheory
namespace FiniteLaw

lemma spinLog_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → Spin) → ℝ) (x : ι → ℝ) :
    spinLog F x=Real.log (∑ s : ι → Spin,(∏ i,q (x i) (s i))*Real.exp (F s)) := by
  unfold spinLog
  rw [Subsingleton.elim (finiteMapDecEq ι) (inferInstance : DecidableEq ι)]

end FiniteLaw

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AveragedEnergyRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped BigOperators Topology

namespace FiniteLaw
lemma spinLog_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (F : (ι → Spin) → ℝ) (x : κ → ℝ) :
    spinLog (fun s : κ → Spin => F (fun i => s (e i))) x = spinLog F (fun i => x (e i)) := by
  classical
  rw [spinLog_eq,spinLog_eq]
  apply congrArg Real.log
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Spin))
  intro s
  change (∏ j : κ,q (x j) (s j))*Real.exp (F (fun i => s (e i))) =
    (∏ i : ι,q (x (e i)) (s (e i)))*Real.exp (F (fun i => s (e i)))
  rw [e.prod_comp (fun j => q (x j) (s j))]
end FiniteLaw

namespace UniversalDictionary
open ConcreteReservoir

lemma reservoirInsertionOn_bound {ι : Type} [Fintype ι] {p : ℕ}
    (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ)
    {D : ℝ} (hF : ∀ s,|F s|≤D) : |reservoirInsertionOn M C H N L u F|≤D :=
  reservoirInsertion_bound M C H N L u (Fintype.card ι) _ (fun _ => hF _)

lemma trialLog_spinLog_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (F : (ι → Spin) → ℝ) :
    trialLog r ζ m (FiniteLaw.spinLog (fun s : κ → Spin => F (fun i => s (e i)))) =
      trialLog r ζ m (FiniteLaw.spinLog F) := by
  have he : FiniteLaw.spinLog (fun s : κ → Spin => F (fun i => s (e i))) =
      (fun x : κ → ℝ => FiniteLaw.spinLog F (fun i => x (e i))) :=
    funext (FiniteLaw.spinLog_reindex e F)
  rw [he]
  exact trialLog_reindex e r (FiniteLaw.spinLog F) m ζ

lemma randomInsertionOn_comparison_tendsto {ι X : Type} [Fintype ι] [MeasurableSpace X]
    {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → (ι → Spin) → ℝ)
    (hFm : Measurable F) {D : ℝ} (hD : 0≤D) (hF : ∀ x s,|F x s|≤D) :
    Tendsto (fun L => limsup (fun n =>
      |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F x) ∂μ)-
        (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ)|) atTop) atTop (𝓝 0) := by
  have h := randomInsertion_comparison_tendsto M hα C H Ns hNs us hcontrol (Fintype.card ι) μ
    (fun x s => F x (fun i => s (Fintype.equivFin ι i)))
    (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp hFm)) hD (fun x _ => hF x _)
  simpa only [reservoirInsertionOn,trialLog_spinLog_reindex] using h

end UniversalDictionary
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
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

lemma abs_integral_le_bound_ae {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} {B : ℝ}
    (h : ∀ᵐ x ∂μ, |f x|≤B) : |∫ x,f x ∂μ|≤B := by
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
      (h.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx))

namespace UniversalDictionary
open ConcreteReservoir

lemma randomInsertionOn_comparison_tendsto_ae {ι X : Type} [Fintype ι] [MeasurableSpace X]
    {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → (ι → Spin) → ℝ)
    (hFm : Measurable F) {D : ℝ} (hD : 0≤D) (hF : ∀ᵐ x ∂μ,∀ s,|F x s|≤D) :
    Tendsto (fun L => limsup (fun n =>
      |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F x) ∂μ)-
        (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ)|) atTop) atTop (𝓝 0) := by
  let G := fun x s => clipReal D (F x s)
  have hm : Measurable G := Measurable.of_eval (fun s => (measurable_clipReal D).comp ((measurable_pi_apply s).comp hFm))
  have he : G =ᵐ[μ] F := hF.mono (fun x hx => funext (fun s => clipReal_eq (hx s)))
  have h := randomInsertionOn_comparison_tendsto M hα C H Ns hNs us hcontrol μ G hm hD
    (fun _ _ => clipReal_bound hD _)
  have hi (L n : ℕ) :
      (∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (G x) ∂μ)=
        ∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F x) ∂μ := by
    apply integral_congr_ae; filter_upwards [he] with x hx; rw [hx]
  have hj (L n : ℕ) :
      (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (G x)) ∂μ)=
        ∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ := by
    apply integral_congr_ae; filter_upwards [he] with x hx; rw [hx]
  simpa only [hi,hj] using h

lemma poissonInsertionOn_comparison_tendsto_ae_oai
    {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
    (μ : (k : ℕ) → Measure (X k)) [∀ k,IsProbabilityMeasure (μ k)]
    (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (hFm : ∀ k,Measurable (F k))
    {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hF : ∀ k,∀ᵐ x ∂μ k,∀ s,|F k x s|≤B+D*k) (ρ : ℝ≥0) :
    Tendsto (fun L => limsup (fun n => ∫ k,
      |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F k x) ∂μ k)-
        (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k)|
      ∂poissonMeasure ρ) atTop) atTop (𝓝 0) := by
  apply poisson_mixture_double_limit ρ _ (B := 2*B) (C := 2*D)
  · intros; exact abs_nonneg _
  · intro k L n
    have h1 := abs_integral_le_bound_ae (μ k) ((hF k).mono (fun x hx =>
      reservoirInsertionOn_bound M C H (Ns L n+1) L (us L n) (F k x) hx))
    have h2 := abs_integral_le_bound_ae (μ k) ((hF k).mono (fun x hx =>
      (trialLog_continuous_bound L (FiniteLaw.spinLog (F k x))
        (FiniteLaw.spinLog_continuous (F k x)) (FiniteLaw.spinLog_bound (F k x) hx) _
        (fun i => gridExponents_pos L i.castSucc)).2
        (reservoirTrialLaw M C H (Ns L n+1) L (us L n))))
    exact (abs_sub _ _).trans (by linarith)
  · intro k
    exact randomInsertionOn_comparison_tendsto_ae M hα C H Ns hNs us hcontrol (μ k) (F k)
      (hFm k) (by positivity) (hF k)

end UniversalDictionary
end DilutedSpinGlass

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae_oai := @OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae_oai
