-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.rootHistory_polarization_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:49.05504+00:00
-- url     : https://prove2.me/submissions/09e86587-802a-44f2-be79-f851a524fc34

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

variable {n : ℕ}

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

theorem leafSum_const {Ω : Type} {n : ℕ} (S : PrescribedTree n)
    (c : ℝ) (x : Sample Ω S) : leafSum S (fun _ => c) x = (leaves S : ℝ) * c := by
  induction S with
  | leaf => simp [leafSum, leaves]
  | @node n k C ih =>
    change (∑ i, leafSum (C i) (fun _ => c) (x i).2) = _
    simp_rw [ih]
    simp only [leaves, Nat.cast_sum, Finset.sum_mul]

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

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteAnalytic
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeMarkLaw
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

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ColoredAnchor
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualTreeSelector
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


noncomputable local instance instDecidableEqEdge_r281364_1 {n : ℕ} (S : PrescribedTree n) : DecidableEq (Edge S) := Classical.decEq _
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ColorIterate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ColorSymmetry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_Polarization
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ColorPolarization
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeSampleProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_LabeledColorHistory
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

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HistorySelector
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_SelectorPolarization
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_UniversalDictionary
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_PrefixProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_MultileafMatrixPointwise
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootMultileafMatrix
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
lemma rootHistory_polarization_sat_oai (hk : 0 < k)
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

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.rootHistory_polarization_sat_oai := @OAI.DilutedSpinGlass.UniversalDictionary.rootHistory_polarization_sat_oai
