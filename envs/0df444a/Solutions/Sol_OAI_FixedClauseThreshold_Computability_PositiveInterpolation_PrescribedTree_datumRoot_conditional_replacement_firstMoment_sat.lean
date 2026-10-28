-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:42:56.774456+00:00
-- url     : https://prove2.me/submissions/ca03d0dc-57b9-4ccb-8fa9-8ecd1462c7a4

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Definitions.Def_OAIQ067A001
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_integral_mixedLog_combination_nonpos_sat

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

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_KernelTower
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeSampling
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProductTowers
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

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_QTreeLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance qTreeLawDecidableEq_r23ba30_1 (type : Type) :
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLogExpansion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootCoefficients
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_RawPatternIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_InsertionPoint
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
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

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularizedNormalization
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TowerPadding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperCommonCoefficient
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

lemma qExpect_expect {A : Type} [Fintype A] (P : FiniteLaw A)
    (m : Fin (n+1) → ℝ) (F : A → PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun S => P.expect (fun a => F a S)) k S =
      P.expect (fun a => qExpect m (F a) k S) := by
  unfold FiniteLaw.expect
  rw [qExpect_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [mul_comm (P.weight a)] using qExpect_mul_const m (F a) (P.weight a) k S

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperRegularized
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory Filter
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

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_NormalizedInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_MixedEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
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

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory Filter
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

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperRootInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
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

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityProxy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperCountState
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
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

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperFreshLocal
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
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
open _root_.MeasureTheory KernelTower
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperConditional
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FirstMomentFresh
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
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

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_InterpolationUpper
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower
open _root_.MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_integrable_norm (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R) :
    Integrable (fun a : UpperDatum p N R => ‖a.1.1‖) (upperDatumLaw (N := N) M Q) :=
  measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integrable_mixedLogAvg (M : Model p) (hM : InterpolationAdmissible M)
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

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integrable_mixedNormalizedAvg (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ)
    (sel : Fin p → Bool) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    Integrable (fun z => mixedNormalizedAvg T Q U V x m z sel t) M.disorder.toMeasure := by
  apply (hM.interaction_integrable.const_mul 2).mono'
    (measurable_mixedNormalizedAvg T Q U V x m sel t).aestronglyMeasurable
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using mixedNormalizedAvg_bound T Q U V x m hm z hz sel ht0 ht

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integrable_mixedEnergyAvg (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ) (sel : Fin p → Bool) :
    Integrable (fun z => mixedEnergyAvg T Q U V x m z sel) M.disorder.toMeasure := by
  apply hM.interaction_integrable.mono' (measurable_mixedEnergyAvg T Q U V x m sel).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using mixedEnergyAvg_bound T Q U V x m hm z sel)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integral_mixedNormalizedAvg_limit (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ) (sel : Fin p → Bool) :
    Tendsto (fun k => ∫ z,mixedNormalizedAvg T Q U V x m z sel (regularization k) ∂M.disorder.toMeasure)
      atTop (𝓝 ((∫ z,mixedEnergyAvg T Q U V x m z sel ∂M.disorder.toMeasure)-
        ∫ z,z.1 (fun _ => false) ∂M.disorder.toMeasure)) := by
  have href : Integrable (fun z : InteractionSample p => z.1 (fun _ => false)) M.disorder.toMeasure :=
    hM.interaction_integrable.mono' (by fun_prop) (ae_of_all _ (fun z => norm_le_pi_norm z.1 _))
  rw [← integral_sub (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integrable_mixedEnergyAvg M hM T Q U V x m hm sel) href]
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

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integral_mixedEnergy_combination_nonpos (M : Model p) (hM : InterpolationAdmissible M)
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
    have hi (sel : Fin p → Bool) := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integrable_mixedLogAvg M hM T Q U V x m hm hpos (fun l => ne_of_gt (hstrict l)) hroot hend sel ht'
    have hn (sel : Fin p → Bool) := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integrable_mixedNormalizedAvg M hM T Q U V x m hstrict sel ht0 ht
    have hd : Integrable (fun z => Real.log (1+regularization k*referenceD z)) M.disorder.toMeasure := by
      convert (hi (fun _ => false)).sub (hn (fun _ => false)) using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      simp only [Pi.sub_apply,mixedNormalizedAvg]
      ring
    simp only [mixedNormalizedAvg]
    rw [integral_sub (hi _) hd,integral_sub (hi _) hd,integral_sub (hi _) hd]
    have hs := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedLog_combination_nonpos_sat M hM T Q U V x m hm hpos
      (fun l => ne_of_gt (hstrict l)) hroot hend j ht0 ht
    rw [hp] at hs ⊢
    nlinarith only [hs]
  have hlim := ((FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun _ => true)).sub
    ((FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun l => decide (l=j))).const_mul (p:ℝ))).add
    ((FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun _ => false)).const_mul ((p-1:ℕ):ℝ))
  have hs := le_of_tendsto hlim (Eventually.of_forall hr)
  rw [hp] at hs ⊢
  nlinarith only [hs]

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integral_mixedRoot_combination_nonpos (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j,0 ≤ m j)
    (hstrict : ∀ j : Fin n,0 < m j.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) :
    (∫ z,mixedRootIncrement T Q U V x m f z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun _ => false) ∂M.disorder.toMeasure) ≤0 := by
  simp only [mixedRootIncrement_eq]
  exact FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedEnergy_combination_nonpos M hM _ Q U V x m hm hpos hstrict hroot hend j

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma freshRoot_mean_sub_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
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
    apply ((integrable_const B).add (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperDatum_integrable_norm M hM Q)).mono' hg.aestronglyMeasurable
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

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma freshRoot_replacement_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
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
  have h := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedRoot_combination_nonpos M hM T Q U V x m hm hpos hstrict hroot hend f j
  simp_rw [mixedRootIncrement_false] at h
  rw [← FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.freshRoot_mean_sub_firstMoment M hM Q T U V x m hstrict f (fun _ => true) hf,
    ← FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.freshRoot_mean_sub_firstMoment M hM Q T U V x m hstrict f (fun d => decide (d=j)) hf] at h
  have hp : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by have := hM.arity; omega : 1≤p),Nat.cast_one]
  rw [hp] at h ⊢
  nlinarith

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma datumRoot_conditional_replacement_firstMoment_sat_oai (M : Model p) (hM : InterpolationAdmissible M)
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
  have h := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.freshRoot_replacement_firstMoment M hM
    (cavityTower T U l (rootMap (fun a => a.2.2) l w)) Q U
    (fun y => V (pathMap (cavityProject l) n y)) x m hm hpos hstrict hroot hend F j
    (fun y => norm_le_pi_norm F y)
  dsimp only [F] at h
  simp only [datumRoot_fresh_true,datumRoot_fresh_selected] at h
  exact h

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

end

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat_oai := @OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat_oai
