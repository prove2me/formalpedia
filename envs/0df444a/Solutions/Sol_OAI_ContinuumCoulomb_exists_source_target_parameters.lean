-- Prove2me | solution 1 for OAI.ContinuumCoulomb.exists_source_target_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:50:55.864183+00:00
-- url     : https://prove2.me/submissions/2b2cf007-1706-406f-9d76-ef761c80c890

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ChargePenalty
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Charge-transfer penalty at half filling

The diagonal part of the finite fermion model keeps long-range direct
Coulomb interactions. A symmetric interaction matrix with bounded absolute
row sums gives a gap against every nonsingly occupied configuration.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

/-- Number conservation forces a charge defect to contain at least one
empty and one doubly occupied site, so its squared charge is at least two. -/
theorem occupation_defect_size {m : ℕ} (occupation : Fin m → Fin 3)
    (hfill : ∑ i, (occupation i : ℕ) = m)
    (hdefect : ¬ ∀ i, occupation i = 1) :
    2 ≤ ∑ i, occupationDeviation occupation i ^ 2 := by
  classical
  let emptySites := Finset.univ.filter (fun i => occupation i = 0)
  have hpoint (i : Fin m) : occupationDeviation occupation i ^ 2 =
      (occupation i : ℕ) - 1 + 2 * (if occupation i = 0 then (1 : ℝ) else 0) := by
    dsimp [occupationDeviation]
    generalize occupation i = k
    fin_cases k <;> norm_num
  have htotal : (∑ i, occupationDeviation occupation i ^ 2) =
      2 * (emptySites.card : ℝ) := by
    simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    have hfillR : (∑ i, ((occupation i : ℕ) : ℝ)) = (m : ℝ) := by exact_mod_cast hfill
    simp only [hfillR, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sub_self, zero_add]
    simp [emptySites]
  obtain ⟨i, hi⟩ := not_forall.mp hdefect
  have hpositive : 0 < ∑ i, occupationDeviation occupation i ^ 2 := by
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg _
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      have hne : occupationDeviation occupation i ≠ 0 := by
        intro hz
        have hv : ((occupation i : ℕ) : ℝ) = 1 := by
          change ((occupation i : ℕ) : ℝ) - 1 = 0 at hz
          linarith
        have hvN : (occupation i : ℕ) = 1 := by exact_mod_cast hv
        exact hi (Fin.ext hvN)
      exact sq_pos_of_ne_zero hne
  have hempty : 0 < emptySites.card := by
    have h : (0 : ℝ) < emptySites.card := by rw [htotal] at hpositive; linarith
    exact_mod_cast h
  have hcard : (1 : ℝ) ≤ emptySites.card := by exact_mod_cast hempty
  rw [htotal]
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ChargeTransfer
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact energy of a virtual hole and double occupancy

A single hop out of the singly occupied subspace creates one empty site and
one doubly occupied site. The full long-range charge penalty on that
configuration is exactly `U - V i j`, so intersite direct repulsion remains
in the superexchange denominator.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem chargeTransfer_deviation {m : ℕ} (hole double k : Fin m) (hne : hole ≠ double) :
    occupationDeviation (chargeTransferOccupation hole double) k =
      (if k = double then (1 : ℝ) else 0) - (if k = hole then (1 : ℝ) else 0) := by
  by_cases hkh : k = hole
  · subst k
    norm_num [chargeTransferOccupation, occupationDeviation, hne]
  · by_cases hkd : k = double
    · subst k
      norm_num [chargeTransferOccupation, occupationDeviation, hne.symm]
    · norm_num [chargeTransferOccupation, occupationDeviation, hkh, hkd]

theorem chargeTransfer_weighted_sum {m : ℕ} (hole double : Fin m) (hne : hole ≠ double)
    (f : Fin m → ℝ) :
    (∑ k, f k * occupationDeviation (chargeTransferOccupation hole double) k) =
      f double - f hole := by
  simp only [chargeTransfer_deviation hole double _ hne, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp

theorem chargeTransfer_deviation_sq_sum {m : ℕ} (hole double : Fin m) (hne : hole ≠ double) :
    (∑ k, occupationDeviation (chargeTransferOccupation hole double) k ^ 2) = 2 := by
  have hpoint (k : Fin m) : occupationDeviation (chargeTransferOccupation hole double) k ^ 2 =
      (if k = double then (1 : ℝ) else 0) + (if k = hole then (1 : ℝ) else 0) := by
    rw [chargeTransfer_deviation hole double k hne]
    by_cases hkh : k = hole
    · subst k
      norm_num [hne]
    · by_cases hkd : k = double <;> norm_num [hkh, hkd, hne.symm]
  simp_rw [hpoint, Finset.sum_add_distrib]
  norm_num

/-- All direct interactions except the hole-double interaction cancel. -/
theorem chargeTransfer_penalty {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (hole double : Fin m) (hne : hole ≠ double)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0) :
    chargePenalty U V (chargeTransferOccupation hole double) = U - V hole double := by
  let d := occupationDeviation (chargeTransferOccupation hole double)
  have hinner (k : Fin m) : (∑ l, V k l * d l) = V k double - V k hole :=
    chargeTransfer_weighted_sum hole double hne (V k)
  have hquad : (∑ k, ∑ l, V k l * d k * d l) = -2 * V hole double := by
    calc
      _ = ∑ k, (V k double - V k hole) * d k := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          _ = (∑ l, V k l * d l) * d k := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro l _
            ring
          _ = _ := by rw [hinner]
      _ = (V double double - V double hole) - (V hole double - V hole hole) :=
        chargeTransfer_weighted_sum hole double hne (fun k => V k double - V k hole)
      _ = _ := by rw [hdiag, hdiag, hsymm double hole]; ring
  unfold chargePenalty
  rw [chargeTransfer_deviation_sq_sum hole double hne]
  change U / 2 * 2 + (1 / 2 : ℝ) * (∑ k, ∑ l, V k l * d k * d l) = _
  rw [hquad]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Operators_CAR
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q)) x) +
    CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

theorem create_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    create i * create j + create j * create i = 0 := by
  refine LinearMap.ext fun x => ?_
  change ExteriorAlgebra.ι ℂ (mode i) * (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * (ExteriorAlgebra.ι ℂ (mode i) * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

theorem annihilate_sq {Q : ℕ} (i : Fin (Q+1)) : annihilate i * annihilate i = 0 := by
  have h : (2 : ℂ) • (annihilate i * annihilate i) = 0 := by
    simpa only [two_smul] using annihilate_anticommute i i
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

theorem create_sq {Q : ℕ} (i : Fin (Q+1)) : create i * create i = 0 := by
  refine LinearMap.ext fun x => ?_
  change ExteriorAlgebra.ι ℂ (mode i) * (ExteriorAlgebra.ι ℂ (mode i) * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Operators_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_create {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j = delta i j • (1 : Module.End ℂ (Space Q)) -
      create j * annihilate i := by
  exact eq_sub_of_add_eq (mixed_car i j)

theorem normal_order_entry {Q : ℕ} (P R : Module.End ℂ (Space Q))
    (i j k l : Fin (Q+1)) :
    (P * create j * annihilate i) * (create k * annihilate l * R) =
      delta i k • (P * create j * annihilate l * R) -
        P * create j * create k * annihilate i * annihilate l * R := by
  calc
    _ = P * create j * (annihilate i * create k) * annihilate l * R := by
      noncomm_ring
    _ = _ := by
      rw [annihilate_create]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
      noncomm_ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardGlobal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Global finite-fermion identities for the Hubbard reduction

These are identities of actual creation and contraction operators on
the finite exterior algebra.  They retain every spectator mode and
therefore do not assume transition signs from the two-site calculation.
-/

noncomputable section

namespace ContinuumCoulomb.HubbardGlobal

open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

theorem transfer_mul (i j k l : Fin (Q + 1)) :
    transfer i j * transfer k l = delta j k • transfer i l -
      create i * create k * annihilate j * annihilate l := by
  simpa only [transfer, one_mul, mul_one] using
    normal_order_entry (1 : Module.End ℂ (Space Q)) 1 j i k l

theorem quartic_exchange (i j k l : Fin (Q + 1)) :
    create i * create k * annihilate j * annihilate l =
      create k * create i * annihilate l * annihilate j := by
  have hc := eq_neg_of_add_eq_zero_left (create_anticommute i k)
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute j l)
  calc
    _ = (create i * create k) * (annihilate j * annihilate l) := by noncomm_ring
    _ = (-(create k * create i)) * (-(annihilate l * annihilate j)) := by rw [hc, ha]
    _ = _ := by ext x; simp

/-- The matrix-unit commutator, proved from the full CAR operators. -/
theorem transfer_commutator (i j k l : Fin (Q + 1)) :
    transfer i j * transfer k l - transfer k l * transfer i j =
      delta j k • transfer i l - delta l i • transfer k j := by
  rw [transfer_mul, transfer_mul, quartic_exchange i j k l]
  abel

theorem number_commute (i j : Fin (Q + 1)) : Commute (number i) (number j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · apply sub_eq_zero.mp
    simpa [number, delta, hij, Ne.symm hij] using transfer_commutator i i j j

theorem number_transfer_commutator (i j k : Fin (Q + 1)) :
    number i * transfer j k - transfer j k * number i =
      (delta i j - delta i k) • transfer j k := by
  have h := transfer_commutator i i j k
  by_cases hij : i = j <;> by_cases hik : i = k <;>
    simp_all [number, delta, eq_comm]
  ext x
  simp

theorem annihilate_number_self (i : Fin (Q + 1)) :
    annihilate i * number i = annihilate i := by
  calc
    _ = (annihilate i * create i) * annihilate i := rfl
    _ = (1 - create i * annihilate i) * annihilate i := by
      rw [annihilate_create]
      simp [delta]
    _ = _ := by simp [sub_mul, mul_assoc, annihilate_sq]

theorem annihilate_number_commute (i j : Fin (Q + 1)) (hij : i ≠ j) :
    Commute (annihilate i) (number j) := by
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute i j)
  calc
    annihilate i * number j = (annihilate i * create j) * annihilate j := rfl
    _ = -(create j * annihilate i) * annihilate j := by
      rw [annihilate_create]
      simp [delta, hij]
    _ = -(create j * (annihilate i * annihilate j)) := by ext x; simp
    _ = number j * annihilate i := by rw [ha]; ext x; simp [number, transfer]

theorem pair_annihilate_siteNumber (i j : Fin (Q + 1)) (hij : i ≠ j) :
    (annihilate i * annihilate j) * (number i + number j) =
      (2 : ℂ) • (annihilate i * annihilate j) := by
  have hleft : (annihilate i * annihilate j) * number i =
      annihilate i * annihilate j := by
    calc
      _ = annihilate i * (annihilate j * number i) := by rw [mul_assoc]
      _ = annihilate i * (number i * annihilate j) := by
        rw [(annihilate_number_commute j i (Ne.symm hij)).eq]
      _ = (annihilate i * number i) * annihilate j := by rw [mul_assoc]
      _ = _ := by rw [annihilate_number_self]
  have hright : (annihilate i * annihilate j) * number j =
      annihilate i * annihilate j := by rw [mul_assoc, annihilate_number_self]
  rw [mul_add, hleft, hright, two_smul]

/-- Local particle number one rules out a pair annihilation, directly
from the CAR; no occupation-basis or sign assumption is needed. -/
theorem pair_annihilate_of_single (i j : Fin (Q + 1)) (hij : i ≠ j)
    (x : Space Q) (hx : (number i + number j) x = x) :
    (annihilate i * annihilate j) x = 0 := by
  have h := LinearMap.congr_fun (pair_annihilate_siteNumber i j hij) x
  change (annihilate i * annihilate j) ((number i + number j) x) =
    (2 : ℂ) • ((annihilate i * annihilate j) x) at h
  rw [hx] at h
  exact add_left_cancel (show
    (annihilate i * annihilate j) x + (annihilate i * annihilate j) x =
      (annihilate i * annihilate j) x + 0 by simpa only [two_smul, add_zero] using h.symm)

theorem transfer_commute_of_distinct (i j k l : Fin (Q + 1))
    (hjk : j ≠ k) (hli : l ≠ i) : Commute (transfer i j) (transfer k l) := by
  apply sub_eq_zero.mp
  simpa [delta, hjk, hli] using transfer_commutator i j k l

theorem transfer_sq_of_ne (i j : Fin (Q + 1)) (hij : i ≠ j) :
    transfer i j * transfer i j = 0 := by
  rw [transfer_mul]
  simp [delta, Ne.symm hij, create_sq]

theorem quartic_number (i j : Fin (Q + 1)) (hij : i ≠ j) :
    create i * create j * annihilate j * annihilate i = number i * number j := by
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute i j)
  calc
    _ = -((create i * create j) * (annihilate i * annihilate j)) := by
      rw [ha]
      ext x
      simp
    _ = _ := by
      rw [number, number, transfer_mul]
      simp only [delta, ite_eq_right hij, zero_smul, zero_sub]
      noncomm_ring

theorem transfer_reverse_product (i j : Fin (Q + 1)) (hij : i ≠ j) :
    transfer i j * transfer j i = number i - number i * number j := by
  rw [transfer_mul, quartic_number i j hij]
  simp [delta, number]

theorem bondTransfer_sq (i j : Fin (Q + 1)) (hij : i ≠ j) :
    bondTransfer i j * bondTransfer i j =
      number i + number j - (2 : ℂ) • (number i * number j) := by
  have hn := (number_commute i j).eq
  unfold bondTransfer
  rw [add_mul, mul_add, mul_add, transfer_sq_of_ne i j hij,
    transfer_sq_of_ne j i (Ne.symm hij), transfer_reverse_product i j hij,
    transfer_reverse_product j i (Ne.symm hij), ← hn]
  simp only [zero_add, add_zero, two_smul]
  abel

/-- A two-transfer exchange identity before imposing occupation
constraints.  It is independent of every spectator mode. -/
theorem transfer_exchange (i j k l : Fin (Q + 1))
    (hjk : j ≠ k) (hlk : l ≠ k) :
    transfer i j * transfer k l = -(transfer i l * transfer k j) := by
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute j l)
  rw [transfer_mul, transfer_mul]
  simp only [delta, ite_eq_right hjk, ite_eq_right hlk, zero_smul, zero_sub, neg_neg]
  calc
    _ = -(create i * create k * (annihilate j * annihilate l)) := by noncomm_ring
    _ = _ := by rw [ha]; ext x; simp

theorem bondTransfer_commute (a b c d : Fin (Q + 1))
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d) :
    Commute (bondTransfer a c) (bondTransfer b d) := by
  exact ((transfer_commute_of_distinct a c b d hcb (Ne.symm had)).add_right
      (transfer_commute_of_distinct a c d b hcd (Ne.symm hab))).add_left
    ((transfer_commute_of_distinct c a b d hab (Ne.symm hcd)).add_right
      (transfer_commute_of_distinct c a d b had (Ne.symm hcb)))

/-- The full hopping-square identity.  The final two terms are the
pair hops, which vanish on singly occupied sites. -/
theorem twoSiteHopping_sq (a b c d : Fin (Q + 1))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    twoSiteHopping a b c d * twoSiteHopping a b c d =
      number a + number b + number c + number d - (2 : ℂ) • spinSwap a b c d -
        (2 : ℂ) • (create a * create b * annihilate c * annihilate d +
          create c * create d * annihilate a * annihilate b) := by
  have hcomm := (bondTransfer_commute a b c d hab had (Ne.symm hbc) hcd).eq
  have hacbd : transfer a c * transfer b d =
      -(create a * create b * annihilate c * annihilate d) := by
    rw [transfer_mul]
    simp [delta, Ne.symm hbc]
  have hcadb : transfer c a * transfer d b =
      -(create c * create d * annihilate a * annihilate b) := by
    rw [transfer_mul]
    simp [delta, had]
  have hacdb := transfer_exchange a c d b hcd hbd
  have hcabd := transfer_exchange c a b d hab (Ne.symm hbd)
  unfold twoSiteHopping
  rw [add_mul, mul_add, mul_add, bondTransfer_sq a c hac, bondTransfer_sq b d hbd,
    ← hcomm]
  unfold bondTransfer
  rw [add_mul, mul_add, mul_add, hacbd, hcadb, hacdb, hcabd]
  unfold spinSwap
  simp only [two_smul]
  abel

/-- The occupied-sector second-order numerator, on a genuine Fock
vector with arbitrary spectators and local particle number one. -/
theorem twoSiteHopping_sq_on_singlyOccupied (a b c d : Fin (Q + 1))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (x : Space Q)
    (hleft : (number a + number b) x = x)
    (hright : (number c + number d) x = x) :
    (twoSiteHopping a b c d * twoSiteHopping a b c d) x =
      (1 - siteHeisenberg a b c d) x := by
  have hpairLeft := pair_annihilate_of_single a b hab x hleft
  have hpairRight := pair_annihilate_of_single c d hcd x hright
  have hQl : (create a * create b * annihilate c * annihilate d) x = 0 := by
    change (create a * create b) ((annihilate c * annihilate d) x) = 0
    rw [hpairRight, map_zero]
  have hQr : (create c * create d * annihilate a * annihilate b) x = 0 := by
    change (create c * create d) ((annihilate a * annihilate b) x) = 0
    rw [hpairLeft, map_zero]
  have htotal : (number a + number b + number c + number d) x = (2 : ℂ) • x := by
    change number a x + number b x = x at hleft
    change number c x + number d x = x at hright
    change number a x + number b x + number c x + number d x = (2 : ℂ) • x
    rw [two_smul]
    rw [add_assoc (number a x + number b x), hleft, hright]
  rw [twoSiteHopping_sq a b c d hab hac had hbc hbd hcd]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [htotal]
  simp only [LinearMap.add_apply, hQl, hQr, add_zero, smul_zero, sub_zero,
    siteHeisenberg, LinearMap.sub_apply, Module.End.one_apply, two_smul]
  abel

/-- Every one-particle transfer preserves the total fermion number. -/
theorem totalNumber_commute_transfer (i j : Fin (Q + 1)) :
    Commute (totalNumber Q) (transfer i j) := by
  apply sub_eq_zero.mp
  unfold totalNumber
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [number_transfer_commutator]
  rw [← Finset.sum_smul]
  simp [delta, Finset.sum_sub_distrib]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardOccupation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual occupation-basis diagonal action for the global Hubbard model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators
variable {Q : ℕ}

theorem annihilate_unoccupied_wedge (i : Fin (Q + 1)) (n : ℕ)
    (w : Fin n → Fin (Q + 1)) (hi : ∀ k, w k ≠ i) :
    annihilate i (ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k))) = 0 := by
  induction n with
  | zero => simp [annihilate]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ι ℂ (mode (w 0)) *
        ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k.succ))) = 0
    rw [CliffordAlgebra.contractLeft_ι_mul]
    have hmode : (LinearMap.proj i : Orbital Q →ₗ[ℂ] ℂ) (mode (w 0)) = 0 := by
      simp [LinearMap.proj, mode, Ne.symm (hi 0)]
    have htail := ih (fun k => w k.succ) (fun k => hi k.succ)
    change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k.succ))) = 0 at htail
    rw [hmode, htail]
    simp

theorem annihilate_unoccupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    annihilate i (fockBasis Q A) = 0 := by
  let S : Set.powersetCard (Fin (Q + 1)) A.card := ⟨A, rfl⟩
  have hn (k : Fin A.card) : Set.powersetCard.ofFinEmbEquiv.symm S k ≠ i := by
    intro h
    apply hi
    rw [← h]
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp ⟨k, rfl⟩
  have h := annihilate_unoccupied_wedge i A.card
    (Set.powersetCard.ofFinEmbEquiv.symm S) hn
  change annihilate i ((Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra S.val) = 0
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simpa only [ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem fockBasis_singleton (i : Fin (Q + 1)) :
    fockBasis Q {i} = ExteriorAlgebra.ι ℂ (mode i) := by
  let S : Set.powersetCard (Fin (Q + 1)) 1 := ⟨{i}, Finset.card_singleton i⟩
  have hi : Set.powersetCard.ofFinEmbEquiv.symm S 0 = i := by
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S
      (Set.powersetCard.ofFinEmbEquiv.symm S 0)).mp ⟨0, rfl⟩
    exact Finset.mem_singleton.mp hm
  change (Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra S.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, Function.comp_apply, hi]
  simp [Pi.basisFun_apply, mode]

theorem create_occupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) : create i (fockBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q + 1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun ℂ (Fin (Q + 1)))
    (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q + 1)) 1)
    (⟨A, rfl⟩ : Set.powersetCard (Fin (Q + 1)) A.card) hd
  change fockBasis Q {i} * fockBasis Q A = 0 at h
  rw [fockBasis_singleton] at h
  exact h

/-- Each actual number operator is diagonal in the full occupation
basis, including every spectator mode. -/
theorem number_basis (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) :
    number i (fockBasis Q A) = if i ∈ A then fockBasis Q A else 0 := by
  by_cases hi : i ∈ A
  · have h := LinearMap.congr_fun (mixed_car i i) (fockBasis Q A)
    change annihilate i (create i (fockBasis Q A)) +
      create i (annihilate i (fockBasis Q A)) =
        (if i = i then (1 : ℂ) else 0) • fockBasis Q A at h
    simpa [hi, create_occupied_basis i A hi, number, transfer] using h
  · simpa [hi, number, transfer] using
      congrArg (create i) (annihilate_unoccupied_basis i A hi)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHamiltonian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed square-lattice Heisenberg source

The finite source is the field-free Heisenberg problem of
Cubitt–Montanaro–Piddock, *Universal quantum Hamiltonians*,
arXiv:1701.05182v4, Theorem 48, Lemma 47 and Section 10.1.
The coordinate-swap action realizes `2 SWAP - I`. Coefficient-rounding
estimates hold for arbitrary many-spin states, including entangled states.
-/

noncomputable section

namespace ContinuumCoulomb

open scoped BigOperators

theorem sourceSpinSwap_apply {n : ℕ} (i j : Fin n)
    (s : SourceSpinBasis n) (k : Fin n) :
    sourceSpinSwap i j s k = s (Equiv.swap i j k) := by
  simp [sourceSpinSwap, Equiv.arrowCongr_apply]

theorem sourceSpinSwap_involutive {n : ℕ} (i j : Fin n) :
    Function.Involutive (sourceSpinSwap i j) := by
  intro s
  funext k
  simp [sourceSpinSwap_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardSpin
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the singly occupied exterior sector with the spin model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

theorem wedgeModes_succ (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1)) :
    wedgeModes (n + 1) v = create (v 0) (wedgeModes n (fun k => v k.succ)) := by
  simp [wedgeModes, ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, create, Function.comp_def]

theorem wedgeModes_replace_zero (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1))
    (i : Fin (Q + 1)) :
    wedgeModes (n + 1) (fun a => if a = 0 then i else v a) =
      create i (wedgeModes n (fun a => v a.succ)) := by
  simp [wedgeModes_succ]

theorem wedgeModes_replace_succ (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1))
    (i : Fin (Q + 1)) (k : Fin n) :
    wedgeModes (n + 1) (fun a => if a = k.succ then i else v a) =
      create (v 0) (wedgeModes n (fun a => if a = k then i else v a.succ)) := by
  have h : (0 : Fin (n + 1)) ≠ k.succ := Ne.symm (Fin.succ_ne_zero k)
  simp [wedgeModes_succ, h]

/-- Even fermion bilinears pass a spectator creator without a sign. -/
theorem transfer_create (i j k : Fin (Q + 1)) :
    transfer i j * create k =
      delta j k • create i + create k * transfer i j := by
  have hc := eq_neg_of_add_eq_zero_left (create_anticommute i k)
  calc
    _ = create i * (annihilate j * create k) := by rw [transfer, mul_assoc]
    _ = delta j k • create i - (create i * create k) * annihilate j := by
      rw [annihilate_create]
      simp only [mul_sub, mul_smul_comm, mul_one, mul_assoc]
    _ = _ := by rw [hc]; ext x; simp [transfer]

/-- The action of a bilinear on an arbitrary wedge is the sum of its
one-particle replacements, with all CAR signs derived. -/
theorem transfer_wedgeModes (i j : Fin (Q + 1)) (n : ℕ)
    (v : Fin n → Fin (Q + 1)) :
    transfer i j (wedgeModes n v) =
      ∑ k, delta j (v k) • wedgeModes n (fun a => if a = k then i else v a) := by
  induction n with
  | zero => simp [wedgeModes, transfer, annihilate]
  | succ n ih =>
    rw [wedgeModes_succ]
    have h := LinearMap.congr_fun (transfer_create i j (v 0))
      (wedgeModes n (fun k => v k.succ))
    change transfer i j (create (v 0) (wedgeModes n (fun k => v k.succ))) =
      delta j (v 0) • create i (wedgeModes n (fun k => v k.succ)) +
        create (v 0) (transfer i j (wedgeModes n (fun k => v k.succ))) at h
    rw [h, ih, map_sum, Fin.sum_univ_succ, wedgeModes_replace_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, wedgeModes_replace_succ]

theorem siteMode_eq_iff (m : ℕ) (i j : Fin (m + 1)) (σ τ : Fin 2) :
    siteMode m i σ = siteMode m j τ ↔ i = j ∧ σ = τ := by
  rw [siteMode, siteMode, Equiv.apply_eq_iff_eq]
  exact Prod.mk_inj

theorem siteMode_ne_of_ne (m : ℕ) (i j : Fin (m + 1)) (hij : i ≠ j) (σ τ : Fin 2) :
    siteMode m i σ ≠ siteMode m j τ :=
  fun h => hij ((siteMode_eq_iff m i j σ τ).mp h).1

/-- Local spin flips act with coefficient one on the ordered wedge;
spectator parities cancel because the operator is an even bilinear. -/
theorem transfer_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i : Fin (m + 1)) (σ τ : Fin 2) :
    transfer (siteMode m i σ) (siteMode m i τ) (spinWedge m s) =
      if s i = τ then spinWedge m (Function.update s i σ) else 0 := by
  unfold spinWedge
  rw [transfer_wedgeModes]
  by_cases his : s i = τ
  · simp only [his, ↓reduceIte]
    rw [Finset.sum_eq_single i]
    · have hδ : delta (siteMode m i τ) (siteMode m i (s i)) = 1 := by
        simp [delta, his]
      rw [hδ, one_smul]
      congr 1
      funext a
      by_cases ha : a = i
      · subst a
        simp
      · simp [ha]
    · intro k _ hki
      have hne : siteMode m i τ ≠ siteMode m k (s k) := by
        intro h
        exact hki ((siteMode_eq_iff m i k τ (s k)).mp h).1.symm
      simp [delta, hne]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · simp only [his, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k _
    have hne : siteMode m i τ ≠ siteMode m k (s k) := by
      intro h
      obtain ⟨hik, hτ⟩ := (siteMode_eq_iff m i k τ (s k)).mp h
      subst k
      exact his hτ.symm
    simp [delta, hne]

theorem sourceSpinSwap_eq_updates (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    sourceSpinSwap i j s = Function.update (Function.update s j (s i)) i (s j) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [sourceSpinSwap_apply]
  · by_cases hkj : k = j
    · subst k
      simp [sourceSpinSwap_apply, Ne.symm hij]
    · simp [sourceSpinSwap_apply, Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

theorem number_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i : Fin (m + 1)) (σ : Fin 2) :
    number (siteMode m i σ) (spinWedge m s) =
      if s i = σ then spinWedge m s else 0 := by
  rw [number, transfer_spinWedge]
  by_cases h : s i = σ
  · rw [← h, Function.update_eq_self]
  · simp [h]

theorem local_number_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i : Fin (m + 1)) :
    (number (siteMode m i 0) + number (siteMode m i 1)) (spinWedge m s) = spinWedge m s := by
  simp only [LinearMap.add_apply, number_spinWedge]
  have h : s i = 0 ∨ s i = 1 := by omega
  rcases h with h | h <;> simp [h]

theorem transfers_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i j : Fin (m + 1)) (hij : i ≠ j) (σ τ ρ υ : Fin 2) :
    (transfer (siteMode m i σ) (siteMode m i τ) *
        transfer (siteMode m j ρ) (siteMode m j υ)) (spinWedge m s) =
      if s i = τ ∧ s j = υ then
        spinWedge m (Function.update (Function.update s j ρ) i σ) else 0 := by
  rw [Module.End.mul_apply, transfer_spinWedge]
  by_cases hj : s j = υ
  · simp only [hj, ↓reduceIte]
    rw [transfer_spinWedge]
    simp [hij]
  · simp [hj]

theorem spinSwap_eq_sum (m : ℕ) (i j : Fin (m + 1)) (hij : i ≠ j) :
    spinSwap (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1) =
      ∑ σ : Fin 2, ∑ τ : Fin 2,
        transfer (siteMode m i σ) (siteMode m i τ) *
          transfer (siteMode m j τ) (siteMode m j σ) := by
  have hc := (transfer_commute_of_distinct (siteMode m j 0) (siteMode m j 1)
    (siteMode m i 1) (siteMode m i 0)
    (siteMode_ne_of_ne m j i (Ne.symm hij) 1 1)
    (siteMode_ne_of_ne m i j hij 0 0)).eq
  simp only [Fin.sum_univ_two, spinSwap, number]
  rw [hc]
  abel

/-- The fermionic exchange is exactly the source coordinate swap,
including its sign and every spectator spin. -/
theorem spinSwap_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    spinSwap (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
        (spinWedge m s) = spinWedge m (sourceSpinSwap i j s) := by
  rw [spinSwap_eq_sum m i j hij]
  simp only [LinearMap.sum_apply]
  simp_rw [transfers_spinWedge m s i j hij]
  rw [Finset.sum_eq_single (s j)]
  · rw [Finset.sum_eq_single (s i)]
    · simp only [and_self, ↓reduceIte]
      rw [← sourceSpinSwap_eq_updates m s i j hij]
    · intro τ _ hτ
      simp [Ne.symm hτ]
    · intro hi
      exact (hi (Finset.mem_univ (s i))).elim
  · intro σ _ hσ
    apply Finset.sum_eq_zero
    intro τ _
    simp [Ne.symm hσ]
  · intro hj
    exact (hj (Finset.mem_univ (s j))).elim

theorem siteHeisenberg_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    siteHeisenberg (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
        (spinWedge m s) =
      (2 : ℂ) • spinWedge m (sourceSpinSwap i j s) - spinWedge m s := by
  simp only [siteHeisenberg, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, spinSwap_spinWedge m s i j hij]

/-- The genuine many-mode hopping square gives the Heisenberg
superexchange numerator on every spin configuration. -/
theorem twoSiteHopping_sq_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    (twoSiteHopping (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1) *
      twoSiteHopping (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1))
        (spinWedge m s) =
      (2 : ℂ) • (spinWedge m s - spinWedge m (sourceSpinSwap i j s)) := by
  have hab : siteMode m i 0 ≠ siteMode m i 1 := by
    intro h
    have hs := (siteMode_eq_iff m i i 0 1).mp h
    norm_num at hs
  have hcd : siteMode m j 0 ≠ siteMode m j 1 := by
    intro h
    have hs := (siteMode_eq_iff m j j 0 1).mp h
    norm_num at hs
  have h := twoSiteHopping_sq_on_singlyOccupied
    (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
    hab (siteMode_ne_of_ne m i j hij 0 0) (siteMode_ne_of_ne m i j hij 0 1)
    (siteMode_ne_of_ne m i j hij 1 0) (siteMode_ne_of_ne m i j hij 1 1) hcd
    (spinWedge m s) (local_number_spinWedge m s i) (local_number_spinWedge m s j)
  rw [LinearMap.sub_apply, Module.End.one_apply, siteHeisenberg_spinWedge m s i j hij] at h
  rw [h]
  simp only [two_smul]
  abel

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardExcitation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual occupation-diagonal inverse and charge-selection rules. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

theorem fockDiagonal_basis (f : Finset (Fin (Q + 1)) → ℂ)
    (A : Finset (Fin (Q + 1))) :
    fockDiagonal f (fockBasis Q A) = f A • fockBasis Q A :=
  (fockBasis Q).constr_basis ℂ _ A

theorem fockDiagonal_coordinate (f : Finset (Fin (Q + 1)) → ℂ)
    (x : Space Q) (A : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (fockDiagonal f x) A = f A * (fockBasis Q).repr x A := by
  have h : ((fockBasis Q).coord A).comp (fockDiagonal f) =
      f A • (fockBasis Q).coord A := by
    apply (fockBasis Q).ext
    intro S
    change (fockBasis Q).repr (fockDiagonal f (fockBasis Q S)) A =
      f A * (fockBasis Q).repr (fockBasis Q S) A
    rw [fockDiagonal_basis, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hSA : S = A
    · subst S
      simp
    · simp [Module.Basis.repr_self, hSA]
  exact LinearMap.congr_fun h x

theorem siteNumber_basis (m : ℕ) (i : Fin (m + 1))
    (A : Finset (Fin ((2 * m + 1) + 1))) :
    siteNumber m i (fockBasis (2 * m + 1) A) =
      ((occupationAt m A i : ℕ) : ℂ) • fockBasis (2 * m + 1) A := by
  simp only [siteNumber, LinearMap.add_apply, number_basis, occupationAt]
  split_ifs <;> simp [two_smul]

theorem siteNumber_eq_diagonal (m : ℕ) (i : Fin (m + 1)) :
    siteNumber m i = fockDiagonal (fun A => ((occupationAt m A i : ℕ) : ℂ)) := by
  apply (fockBasis (2 * m + 1)).ext
  intro A
  rw [siteNumber_basis, fockDiagonal_basis]

theorem numberEigen_coordinate_zero (m : ℕ) (i : Fin (m + 1))
    (x : Space (2 * m + 1)) (η : ℂ) (hx : siteNumber m i x = η • x)
    (A : Finset (Fin ((2 * m + 1) + 1)))
    (hne : ((occupationAt m A i : ℕ) : ℂ) ≠ η) :
    (fockBasis (2 * m + 1)).repr x A = 0 := by
  have h := congrArg (fun y => (fockBasis (2 * m + 1)).repr y A) hx
  rw [siteNumber_eq_diagonal, fockDiagonal_coordinate, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at h
  have hz : (((occupationAt m A i : ℕ) : ℂ) - η) *
      (fockBasis (2 * m + 1)).repr x A = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

/-- A joint local-number eigenvector has the corresponding value of
every actual occupation-diagonal operator. -/
theorem occupationDiagonal_eigen (m : ℕ) (f : (Fin (m + 1) → Fin 3) → ℂ)
    (o : Fin (m + 1) → Fin 3) (x : Space (2 * m + 1))
    (hx : ∀ i, siteNumber m i x = ((o i : ℕ) : ℂ) • x) :
    occupationDiagonal m f x = f o • x := by
  apply (fockBasis (2 * m + 1)).repr.injective
  ext A
  simp only [occupationDiagonal, fockDiagonal_coordinate, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  by_cases ho : occupationAt m A = o
  · rw [ho]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp ho
    have hne : ((occupationAt m A i : ℕ) : ℂ) ≠ ((o i : ℕ) : ℂ) := by
      intro h
      apply hi
      apply Fin.ext
      exact_mod_cast h
    rw [numberEigen_coordinate_zero m i x _ (hx i) A hne]
    simp

theorem lowProjection_eq_zero_of_numberEigen (m : ℕ) (i : Fin (m + 1))
    (x : Space (2 * m + 1)) (η : ℂ) (hx : siteNumber m i x = η • x) (hη : η ≠ 1) :
    lowProjection m x = 0 := by
  apply (fockBasis (2 * m + 1)).repr.injective
  ext A
  simp only [lowProjection, occupationDiagonal, fockDiagonal_coordinate, map_zero,
    Finsupp.zero_apply]
  by_cases hs : ∀ k, occupationAt m A k = 1
  · have hne : ((occupationAt m A i : ℕ) : ℂ) ≠ η := by
      simpa only [hs i, Fin.val_one, Nat.cast_one] using Ne.symm hη
    rw [numberEigen_coordinate_zero m i x η hx A hne]
    simp
  · simp [hs]

theorem siteMode_delta_sum (m : ℕ) (k i : Fin (m + 1)) (σ : Fin 2) :
    delta (siteMode m k 0) (siteMode m i σ) +
      delta (siteMode m k 1) (siteMode m i σ) = if k = i then 1 else 0 := by
  by_cases hki : k = i
  · subst k
    fin_cases σ <;> simp [delta, siteMode_eq_iff]
  · simp [delta, siteMode_eq_iff, hki]

theorem siteNumber_transfer_commutator (m : ℕ) (k i j : Fin (m + 1)) (σ τ : Fin 2) :
    siteNumber m k * transfer (siteMode m i σ) (siteMode m j τ) -
      transfer (siteMode m i σ) (siteMode m j τ) * siteNumber m k =
        chargeShift k i j • transfer (siteMode m i σ) (siteMode m j τ) := by
  let E := transfer (siteMode m i σ) (siteMode m j τ)
  let n₀ := number (siteMode m k 0)
  let n₁ := number (siteMode m k 1)
  have h₀ := number_transfer_commutator (siteMode m k 0) (siteMode m i σ) (siteMode m j τ)
  have h₁ := number_transfer_commutator (siteMode m k 1) (siteMode m i σ) (siteMode m j τ)
  change (n₀ + n₁) * E - E * (n₀ + n₁) = chargeShift k i j • E
  calc
    _ = (n₀ * E - E * n₀) + (n₁ * E - E * n₁) := by noncomm_ring
    _ = ((delta (siteMode m k 0) (siteMode m i σ) -
          delta (siteMode m k 0) (siteMode m j τ)) +
        (delta (siteMode m k 1) (siteMode m i σ) -
          delta (siteMode m k 1) (siteMode m j τ))) • E := by
      rw [h₀, h₁, ← add_smul]
    _ = ((delta (siteMode m k 0) (siteMode m i σ) +
          delta (siteMode m k 1) (siteMode m i σ)) -
        (delta (siteMode m k 0) (siteMode m j τ) +
          delta (siteMode m k 1) (siteMode m j τ))) • E := by
      congr 1
      ring
    _ = _ := by rw [siteMode_delta_sum, siteMode_delta_sum]; rfl

/-- Hopping shifts the destination and source local particle numbers
by exactly plus and minus one. -/
theorem siteNumber_transfer_eigen (m : ℕ) (k i j : Fin (m + 1)) (σ τ : Fin 2)
    (x : Space (2 * m + 1)) (η : ℂ) (hx : siteNumber m k x = η • x) :
    siteNumber m k (transfer (siteMode m i σ) (siteMode m j τ) x) =
      (η + chargeShift k i j) • transfer (siteMode m i σ) (siteMode m j τ) x := by
  have h := LinearMap.congr_fun (siteNumber_transfer_commutator m k i j σ τ) x
  change siteNumber m k (transfer (siteMode m i σ) (siteMode m j τ) x) -
    transfer (siteMode m i σ) (siteMode m j τ) (siteNumber m k x) =
      chargeShift k i j • transfer (siteMode m i σ) (siteMode m j τ) x at h
  rw [hx, map_smul] at h
  calc
    _ = chargeShift k i j • transfer (siteMode m i σ) (siteMode m j τ) x +
        η • transfer (siteMode m i σ) (siteMode m j τ) x := (sub_eq_iff_eq_add).mp h
    _ = _ := by rw [add_smul]; abel

theorem siteNumber_spinWedge (m : ℕ) (s : SourceSpinBasis (m + 1)) (k : Fin (m + 1)) :
    siteNumber m k (spinWedge m s) = (1 : ℂ) • spinWedge m s := by
  simpa only [siteNumber, one_smul] using local_number_spinWedge m s k

theorem lowProjection_spinWedge (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    lowProjection m (spinWedge m s) = spinWedge m s := by
  have h := occupationDiagonal_eigen m (fun o => if ∀ i, o i = 1 then 1 else 0)
    (fun _ => 1) (spinWedge m s) (fun k => by simpa using siteNumber_spinWedge m s k)
  simpa [lowProjection] using h

/-- A genuine single hop creates the exact hole/double virtual charge
sector. Its inverse denominator retains the direct repulsion `V i j`. -/
theorem chargeInverse_transfer_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (s : SourceSpinBasis (m + 1)) (i j : Fin (m + 1)) (hij : i ≠ j) (σ τ : Fin 2) :
    chargeInverse m U V (transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s)) =
      (((U - V i j)⁻¹ : ℝ) : ℂ) •
        transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s) := by
  have hvalue (k : Fin (m + 1)) :
      1 + chargeShift k i j = ((chargeTransferOccupation j i k : ℕ) : ℂ) := by
    by_cases hki : k = i
    · subst k
      norm_num [chargeShift, chargeTransferOccupation, hij]
    · by_cases hkj : k = j
      · subst k
        norm_num [chargeShift, chargeTransferOccupation, Ne.symm hij]
      · norm_num [chargeShift, chargeTransferOccupation, hki, hkj]
  have heigen (k : Fin (m + 1)) :
      siteNumber m k (transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s)) =
        ((chargeTransferOccupation j i k : ℕ) : ℂ) •
          transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s) := by
    rw [← hvalue]
    exact siteNumber_transfer_eigen m k i j σ τ _ _ (siteNumber_spinWedge m s k)
  have h := occupationDiagonal_eigen m
    (fun o => (((chargePenalty U V o)⁻¹ : ℝ) : ℂ))
    (chargeTransferOccupation j i)
    (transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s)) heigen
  simpa only [chargeInverse, chargeTransfer_penalty U V j i (Ne.symm hij) hsymm hdiag,
    hsymm j i] using h

/-- Two transfers cannot return to the singly occupied sector unless
their oriented site changes are exact reverses. -/
theorem lowProjection_transfer_transfer_zero (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j k l : Fin (m + 1)) (hij : i ≠ j) (hreverse : ¬(i = l ∧ j = k))
    (σ τ ρ υ : Fin 2) :
    lowProjection m
      (transfer (siteMode m i σ) (siteMode m j τ)
        (transfer (siteMode m k ρ) (siteMode m l υ) (spinWedge m s))) = 0 := by
  have heigen (r : Fin (m + 1)) :
      siteNumber m r
          (transfer (siteMode m i σ) (siteMode m j τ)
            (transfer (siteMode m k ρ) (siteMode m l υ) (spinWedge m s))) =
        ((1 + chargeShift r k l) + chargeShift r i j) •
          transfer (siteMode m i σ) (siteMode m j τ)
            (transfer (siteMode m k ρ) (siteMode m l υ) (spinWedge m s)) :=
    siteNumber_transfer_eigen m r i j σ τ _ _
      (siteNumber_transfer_eigen m r k l ρ υ _ _ (siteNumber_spinWedge m s r))
  by_cases hil : i = l
  · have hjk : j ≠ k := fun h => hreverse ⟨hil, h⟩
    have hjl : j ≠ l := fun h => hij (hil.trans h.symm)
    apply lowProjection_eq_zero_of_numberEigen m j _ _ (heigen j)
    norm_num [chargeShift, hjk, hjl, Ne.symm hij]
  · apply lowProjection_eq_zero_of_numberEigen m i _ _ (heigen i)
    by_cases hik : i = k
    · subst k
      norm_num [chargeShift, hij, hil]
    · norm_num [chargeShift, hij, hil, hik]

theorem chargeInverse_hopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (s : SourceSpinBasis (m + 1)) (i j : Fin (m + 1)) (hij : i ≠ j) :
    chargeInverse m U V (siteHopping m i j (spinWedge m s)) =
      (((U - V i j)⁻¹ : ℝ) : ℂ) • siteHopping m i j (spinWedge m s) := by
  simp [siteHopping, twoSiteHopping, bondTransfer, LinearMap.add_apply, map_add,
    chargeInverse_transfer_spinWedge m U V hsymm hdiag s i j hij,
    chargeInverse_transfer_spinWedge m U V hsymm hdiag s j i (Ne.symm hij),
    hsymm j i, smul_add]

/-- Different unordered edges have zero second-order low compression,
with every spin channel and fermionic spectator retained. -/
theorem lowProjection_hopping_hopping_zero (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j k l : Fin (m + 1)) (hij : i ≠ j)
    (hsame : ¬(i = k ∧ j = l)) (hreverse : ¬(i = l ∧ j = k)) :
    lowProjection m (siteHopping m i j (siteHopping m k l (spinWedge m s))) = 0 := by
  have hsame' : ¬(j = l ∧ i = k) := fun h => hsame ⟨h.2, h.1⟩
  have hreverse' : ¬(j = k ∧ i = l) := fun h => hreverse ⟨h.2, h.1⟩
  simp [siteHopping, twoSiteHopping, bondTransfer, LinearMap.add_apply, map_add,
    lowProjection_transfer_transfer_zero m s i j k l hij hreverse,
    lowProjection_transfer_transfer_zero m s i j l k hij hsame,
    lowProjection_transfer_transfer_zero m s j i k l (Ne.symm hij) hsame',
    lowProjection_transfer_transfer_zero m s j i l k (Ne.symm hij) hreverse']

/-- The same-edge inverse compression, with the exact Coulomb-modified
denominator, acts as the expected Heisenberg superexchange numerator. -/
theorem hopping_inverse_hopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (s : SourceSpinBasis (m + 1)) (i j : Fin (m + 1)) (hij : i ≠ j) :
    lowProjection m (siteHopping m i j (chargeInverse m U V (siteHopping m i j (spinWedge m s)))) =
      (((U - V i j)⁻¹ : ℝ) : ℂ) •
        ((2 : ℂ) • (spinWedge m s - spinWedge m (sourceSpinSwap i j s))) := by
  rw [chargeInverse_hopping_spinWedge m U V hsymm hdiag s i j hij, map_smul, map_smul]
  have h := twoSiteHopping_sq_spinWedge m s i j hij
  change siteHopping m i j (siteHopping m i j (spinWedge m s)) = _ at h
  rw [h, map_smul, map_sub, lowProjection_spinWedge, lowProjection_spinWedge]

/-- All distinct-edge terms of the actual inverse compression vanish. -/
theorem cross_hopping_inverse_hopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (s : SourceSpinBasis (m + 1)) (i j k l : Fin (m + 1)) (hij : i ≠ j) (hkl : k ≠ l)
    (hsame : ¬(i = k ∧ j = l)) (hreverse : ¬(i = l ∧ j = k)) :
    lowProjection m (siteHopping m i j (chargeInverse m U V (siteHopping m k l (spinWedge m s)))) =
      0 := by
  rw [chargeInverse_hopping_spinWedge m U V hsymm hdiag s k l hkl, map_smul, map_smul,
    lowProjection_hopping_hopping_zero m s i j k l hij hsame hreverse, smul_zero]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GlobalSuperexchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global Hubbard second-order compression on the spin sector. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Edge : Type*} [Fintype Edge]

/-- Only the matching graph edge survives an inverse compression. -/
theorem hopping_inverse_graphHopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (s : SourceSpinBasis (m + 1)) (e : Edge) :
    lowProjection m (siteHopping m (left e) (right e)
      (chargeInverse m U V (graphHopping m left right t (spinWedge m s)))) =
        t e • (((U - V (left e) (right e))⁻¹ : ℝ) : ℂ) •
          ((2 : ℂ) • (spinWedge m s - spinWedge m (sourceSpinSwap (left e) (right e) s))) := by
  classical
  simp only [graphHopping, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  rw [Finset.sum_eq_single e]
  · rw [hopping_inverse_hopping_spinWedge m U V hsymm hdiag s (left e) (right e) (hloop e)]
  · intro f _ hfe
    obtain ⟨hparallel, hreverse⟩ := hsimple e f (Ne.symm hfe)
    rw [cross_hopping_inverse_hopping_spinWedge m U V hsymm hdiag s
      (left e) (right e) (left f) (right f) (hloop e) (hloop f) hparallel hreverse, smul_zero]
  · intro he
    exact (he (Finset.mem_univ e)).elim

/-- The actual global inverse compression is the sum of the local
exchange terms, with the Coulomb-corrected denominator on every edge. -/
theorem graphHopping_inverse_graphHopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (s : SourceSpinBasis (m + 1)) :
    lowProjection m (graphHopping m left right t
      (chargeInverse m U V (graphHopping m left right t (spinWedge m s)))) =
        ∑ e, t e ^ 2 • (((U - V (left e) (right e))⁻¹ : ℝ) : ℂ) •
          ((2 : ℂ) • (spinWedge m s - spinWedge m (sourceSpinSwap (left e) (right e) s))) := by
  classical
  change lowProjection m ((∑ e, t e • siteHopping m (left e) (right e))
    (chargeInverse m U V (graphHopping m left right t (spinWedge m s)))) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro e _
  rw [hopping_inverse_graphHopping_spinWedge m U V hsymm hdiag left right t hloop hsimple s e]
  simp only [smul_smul, pow_two, mul_assoc]

/-- Choosing `t_e² = J_e (U-V_e)` gives the genuine Heisenberg inverse
term, including the scalar `-J_e I` on every edge. -/
theorem graphSuperexchange_calibrated (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * ((U - V (left e) (right e) : ℝ) : ℂ))
    (s : SourceSpinBasis (m + 1)) :
    -(lowProjection m (graphHopping m left right t
      (chargeInverse m U V (graphHopping m left right t (spinWedge m s))))) =
        ∑ e, J e • ((siteHeisenberg (siteMode m (left e) 0) (siteMode m (left e) 1)
          (siteMode m (right e) 0) (siteMode m (right e) 1) - 1) (spinWedge m s)) := by
  rw [graphHopping_inverse_graphHopping_spinWedge m U V hsymm hdiag left right t hloop hsimple s,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hgapC : ((U - V (left e) (right e) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgap e
  have hcoeff : t e ^ 2 * ((((U - V (left e) (right e))⁻¹ : ℝ) : ℂ)) = J e := by
    rw [hcal e, Complex.ofReal_inv, mul_assoc, mul_inv_cancel₀ hgapC, mul_one]
  rw [smul_smul, hcoeff]
  simp only [LinearMap.sub_apply, Module.End.one_apply,
    siteHeisenberg_spinWedge m s (left e) (right e) (hloop e), smul_sub, two_smul, smul_add]
  abel

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinEmbedding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical, norm-preserving embedding of the spin sector in Fock space. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

theorem spinOccupationSet_injective (m : ℕ) : Function.Injective (spinOccupationSet m) := by
  intro s t h
  have hS : Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s) =
      Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m t) := Subtype.ext h
  have hE := Set.powersetCard.ofFinEmbEquiv.injective hS
  funext i
  have hi := congrArg (fun f : Fin (m + 1) ↪o Fin ((2 * m + 1) + 1) => f i) hE
  exact ((siteMode_eq_iff m i i (s i) (t i)).mp hi).2

/-- The ordered spin wedge is exactly a canonical occupation-basis
vector, with no arbitrary normalization or phase. -/
theorem spinWedge_eq_fockBasis (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    spinWedge m s = fockBasis (2 * m + 1) (spinOccupationSet m s) := by
  let S := Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)
  change wedgeModes (m + 1) (fun i => siteMode m i (s i)) =
    (Pi.basisFun ℂ (Fin ((2 * m + 1) + 1))).ExteriorAlgebra S.val
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, S, Equiv.symm_apply_apply]
  unfold wedgeModes
  congr 1
  funext i
  rw [Function.comp_apply, Pi.basisFun_apply]
  rfl

theorem spinEmbedding_coordinate (m : ℕ) (u : SourceSpinVector (m + 1))
    (s : SourceSpinBasis (m + 1)) :
    (fockBasis (2 * m + 1)).repr (spinEmbedding m u) (spinOccupationSet m s) = u s := by
  simp [spinEmbedding, spinWedge_eq_fockBasis, Module.Basis.repr_self, Finsupp.single_apply,
    (spinOccupationSet_injective m).eq_iff]

theorem spinEmbedding_coordinate_outside (m : ℕ) (u : SourceSpinVector (m + 1))
    (A : Finset (Fin ((2 * m + 1) + 1)))
    (hA : ∀ s, spinOccupationSet m s ≠ A) :
    (fockBasis (2 * m + 1)).repr (spinEmbedding m u) A = 0 := by
  simp [spinEmbedding, spinWedge_eq_fockBasis, Module.Basis.repr_self, hA]

theorem spinEmbedding_swap (m : ℕ) (u : SourceSpinVector (m + 1))
    (i j : Fin (m + 1)) :
    (∑ s, u s • spinWedge m (sourceSpinSwap i j s)) =
      spinEmbedding m (fun s => u (sourceSpinSwap i j s)) := by
  change (∑ s, u s • spinWedge m (sourceSpinSwap i j s)) =
    ∑ s, u (sourceSpinSwap i j s) • spinWedge m s
  have h := (sourceSpinSwap i j).sum_comp
    (fun s => u s • spinWedge m (sourceSpinSwap i j s))
  have hswap (s : SourceSpinBasis (m + 1)) :
      sourceSpinSwap i j (sourceSpinSwap i j s) = s := sourceSpinSwap_involutive i j s
  simp_rw [hswap] at h
  exact h.symm

/-- The actual Fock Heisenberg operator intertwines the source action
on arbitrary, possibly entangled, spin vectors. -/
theorem spinEmbedding_heisenberg (m : ℕ) (u : SourceSpinVector (m + 1))
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    siteHeisenberg (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
        (spinEmbedding m u) = spinEmbedding m (sourceHeisenbergAction i j u) := by
  change siteHeisenberg (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
    (∑ s, u s • spinWedge m s) = _
  rw [map_sum]
  simp_rw [map_smul, siteHeisenberg_spinWedge m _ i j hij]
  have hpoint (s : SourceSpinBasis (m + 1)) :
      u s • ((2 : ℂ) • spinWedge m (sourceSpinSwap i j s) - spinWedge m s) =
        (2 : ℂ) • (u s • spinWedge m (sourceSpinSwap i j s)) - u s • spinWedge m s := by
    simp [smul_sub, smul_smul, mul_comm]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, spinEmbedding_swap]
  change (2 : ℂ) • spinEmbedding m (fun s => u (sourceSpinSwap i j s)) - spinEmbedding m u = _
  rw [← map_smul, ← map_sub]
  congr 1

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial operator bounds from the actual exterior occupation basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Q : ℕ}

/-- A creator sends an unoccupied canonical basis vector to the inserted
occupation with its actual exterior permutation sign. -/
theorem create_unoccupied_basis_signed (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧
      create i (fockBasis Q A) = c • fockBasis Q (insert i A) := by
  let S : Set.powersetCard (Fin (Q + 1)) 1 := ⟨{i}, Finset.card_singleton i⟩
  let T : Set.powersetCard (Fin (Q + 1)) A.card := ⟨A, rfl⟩
  have hd : Disjoint S.val T.val := by simpa only [S, T, Finset.disjoint_singleton_left]
  have h := ExteriorAlgebra.basis_mul_of_disjoint
    (Pi.basisFun ℂ (Fin (Q + 1))) S T hd
  have hset : (Set.powersetCard.disjUnion hd).val = insert i A := by
    ext k
    simp [Set.powersetCard.disjUnion, S, T]
  change fockBasis Q {i} * fockBasis Q A =
    (Set.powersetCard.permOfDisjoint hd).sign •
      fockBasis Q (Set.powersetCard.disjUnion hd).val at h
  rw [fockBasis_singleton, hset] at h
  rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hd).sign with hs | hs
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa only [hs, one_smul, create, LinearMap.coe_mk, AddHom.coe_mk] using h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simpa only [hs, Units.neg_smul, one_smul, neg_smul,
      create, LinearMap.coe_mk, AddHom.coe_mk] using h

theorem creationCoefficient_signed (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    creationCoefficient i A = 1 ∨ creationCoefficient i A = -1 := by
  obtain ⟨c, hc, h⟩ := create_unoccupied_basis_signed i A hi
  have heq : creationCoefficient i A = c := by
    simp [creationCoefficient, h]
  simpa only [heq] using hc

theorem creationCoefficient_occupied (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) : creationCoefficient i A = 0 := by
  simp [creationCoefficient, create_occupied_basis i A hi]

theorem create_basis (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) :
    create i (fockBasis Q A) = creationCoefficient i A • fockBasis Q (insert i A) := by
  by_cases hi : i ∈ A
  · simp [create_occupied_basis i A hi, creationCoefficient_occupied i A hi]
  · obtain ⟨c, _, hc⟩ := create_unoccupied_basis_signed i A hi
    have heq : creationCoefficient i A = c := by simp [creationCoefficient, hc]
    rw [heq, hc]

theorem annihilate_create_unoccupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    annihilate i (create i (fockBasis Q A)) = fockBasis Q A := by
  have h := LinearMap.congr_fun (mixed_car i i) (fockBasis Q A)
  change annihilate i (create i (fockBasis Q A)) +
    number i (fockBasis Q A) = (if i = i then (1 : ℂ) else 0) • fockBasis Q A at h
  simpa [number_basis, hi] using h

theorem annihilate_occupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) :
    annihilate i (fockBasis Q A) =
      creationCoefficient i (A.erase i) • fockBasis Q (A.erase i) := by
  have h := annihilate_create_unoccupied_basis i (A.erase i) (Finset.notMem_erase _ _)
  rw [create_basis, Finset.insert_erase hi, map_smul] at h
  have hc : creationCoefficient i (A.erase i) * creationCoefficient i (A.erase i) = 1 := by
    rcases creationCoefficient_signed i (A.erase i) (Finset.notMem_erase _ _) with hc | hc
    all_goals simp [hc]
  calc
    _ = creationCoefficient i (A.erase i) •
        (creationCoefficient i (A.erase i) • annihilate i (fockBasis Q A)) := by
      rw [smul_smul, hc, one_smul]
    _ = _ := congrArg (fun x => creationCoefficient i (A.erase i) • x) h

theorem create_coordinate (i : Fin (Q + 1)) (x : Space Q)
    (B : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (create i x) B =
      if i ∈ B then creationCoefficient i (B.erase i) * (fockBasis Q).repr x (B.erase i)
      else 0 := by
  classical
  have h : create i x = ∑ A, (fockBasis Q).repr x A • create i (fockBasis Q A) := by
    simp only [← map_smul]
    rw [← map_sum, (fockBasis Q).sum_repr]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  simp only [create_basis, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ B
  · rw [ite_eq_left hi, Finset.sum_eq_single (B.erase i)]
    · simp [Finset.insert_erase hi, mul_comm]
    · intro A _ hA
      by_cases hiA : i ∈ A
      · simp [creationCoefficient_occupied i A hiA]
      · have hne : insert i A ≠ B := by
          intro hAB
          apply hA
          have he := congrArg (Finset.erase · i) hAB
          simpa only [Finset.erase_insert hiA] using he
        simp [Module.Basis.repr_self, hne]
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro A _
    have hne : insert i A ≠ B := by
      intro hAB
      exact hi (hAB ▸ Finset.mem_insert_self i A)
    simp [Module.Basis.repr_self, hne]

theorem annihilate_coordinate (i : Fin (Q + 1)) (x : Space Q)
    (B : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (annihilate i x) B =
      if i ∉ B then creationCoefficient i B * (fockBasis Q).repr x (insert i B)
      else 0 := by
  classical
  have h : annihilate i x =
      ∑ A, (fockBasis Q).repr x A • annihilate i (fockBasis Q A) := by
    simp only [← map_smul]
    rw [← map_sum, (fockBasis Q).sum_repr]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  by_cases hi : i ∈ B
  · rw [ite_eq_right (not_not.mpr hi)]
    apply Finset.sum_eq_zero
    intro A _
    by_cases hiA : i ∈ A
    · rw [annihilate_occupied_basis i A hiA]
      have hne : A.erase i ≠ B := by
        intro he
        exact (Finset.notMem_erase i A) (he.symm ▸ hi)
      simp [Module.Basis.repr_self, hne]
    · simp [annihilate_unoccupied_basis i A hiA]
  · rw [ite_eq_left hi, Finset.sum_eq_single (insert i B)]
    · rw [annihilate_occupied_basis i (insert i B) (Finset.mem_insert_self _ _),
        Finset.erase_insert hi]
      simp [mul_comm]
    · intro A _ hA
      by_cases hiA : i ∈ A
      · rw [annihilate_occupied_basis i A hiA]
        have hne : A.erase i ≠ B := by
          intro he
          exact hA ((Finset.insert_erase hiA).symm.trans (congrArg (insert i) he))
        simp [Module.Basis.repr_self, hne]
      · simp [annihilate_unoccupied_basis i A hiA]
    · simp

theorem creationCoefficient_conj (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) :
    star (creationCoefficient i A) = creationCoefficient i A := by
  by_cases hi : i ∈ A
  · simp [creationCoefficient_occupied i A hi]
  · rcases creationCoefficient_signed i A hi with hc | hc
    all_goals simp [hc]

/-- The creator and contraction are actual adjoints in the canonical
occupation norm; the signs come from the exterior basis above. -/
theorem fock_inner_create_annihilate (i : Fin (Q + 1)) (x y : Space Q) :
    (∑ B, star ((fockBasis Q).repr (create i x) B) * (fockBasis Q).repr y B) =
      ∑ A, star ((fockBasis Q).repr x A) * (fockBasis Q).repr (annihilate i y) A := by
  classical
  have hleft (B : Finset (Fin (Q + 1))) :
      star ((fockBasis Q).repr (create i x) B) * (fockBasis Q).repr y B =
        if i ∈ B then creationCoefficient i (B.erase i) *
          star ((fockBasis Q).repr x (B.erase i)) * (fockBasis Q).repr y B else 0 := by
    rw [create_coordinate]
    split_ifs <;> simp [star_mul, creationCoefficient_conj, mul_comm, mul_left_comm]
  have hright (A : Finset (Fin (Q + 1))) :
      star ((fockBasis Q).repr x A) * (fockBasis Q).repr (annihilate i y) A =
        if i ∉ A then creationCoefficient i A *
          star ((fockBasis Q).repr x A) * (fockBasis Q).repr y (insert i A) else 0 := by
    rw [annihilate_coordinate]
    split_ifs <;> simp [mul_comm, mul_left_comm]
  simp_rw [hleft, hright]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∈ A) _ (by simp),
    Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∉ A) _ (by simp)]
  have h := (insertModeEquiv i).sum_comp (fun B => creationCoefficient i (B.val.erase i) *
    star ((fockBasis Q).repr x (B.val.erase i)) * (fockBasis Q).repr y B.val)
  simp_rw [insertModeEquiv_erase, insertModeEquiv_val] at h
  exact h.symm

theorem fockMass_create (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (create i x) =
      ∑ A : {A : Finset (Fin (Q + 1)) // i ∉ A},
        Complex.normSq ((fockBasis Q).repr x A.val) := by
  classical
  have hpoint (B : Finset (Fin (Q + 1))) :
      Complex.normSq ((fockBasis Q).repr (create i x) B) =
        if i ∈ B then Complex.normSq ((fockBasis Q).repr x (B.erase i)) else 0 := by
    rw [create_coordinate]
    by_cases hi : i ∈ B
    · simp only [hi, ↓reduceIte]
      rcases creationCoefficient_signed i (B.erase i) (Finset.notMem_erase _ _) with hc | hc
      all_goals simp [hc]
    · simp [hi]
  unfold fockMass
  simp_rw [hpoint]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∈ A) _ (by simp)]
  have h := (insertModeEquiv i).sum_comp
    (fun B => Complex.normSq ((fockBasis Q).repr x (B.val.erase i)))
  simp_rw [insertModeEquiv_erase] at h
  exact h.symm

theorem fockMass_annihilate (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (annihilate i x) =
      ∑ A : {A : Finset (Fin (Q + 1)) // i ∈ A},
        Complex.normSq ((fockBasis Q).repr x A.val) := by
  classical
  have hpoint (B : Finset (Fin (Q + 1))) :
      Complex.normSq ((fockBasis Q).repr (annihilate i x) B) =
        if i ∉ B then Complex.normSq ((fockBasis Q).repr x (insert i B)) else 0 := by
    rw [annihilate_coordinate]
    by_cases hi : i ∉ B
    · simp only [hi]
      rcases creationCoefficient_signed i B hi with hc | hc
      all_goals simp [hc]
    · simp [hi]
  unfold fockMass
  simp_rw [hpoint]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∉ A) _ (by simp)]
  have h := (insertModeEquiv i).symm.sum_comp
    (fun B => Complex.normSq ((fockBasis Q).repr x (insert i B.val)))
  simp_rw [insertModeEquiv_symm_insert] at h
  exact h.symm

theorem fockMass_create_le (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (create i x) ≤ fockMass x := by
  classical
  rw [fockMass_create]
  have h := Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin (Q + 1)) => i ∉ A)
    (fun A => Complex.normSq ((fockBasis Q).repr x A))
  have hnonneg : 0 ≤ ∑ A : {A : Finset (Fin (Q + 1)) // ¬i ∉ A},
      Complex.normSq ((fockBasis Q).repr x A.val) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change _ ≤ ∑ A, Complex.normSq ((fockBasis Q).repr x A)
  linarith

theorem fockMass_annihilate_le (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (annihilate i x) ≤ fockMass x := by
  classical
  rw [fockMass_annihilate]
  have h := Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin (Q + 1)) => i ∈ A)
    (fun A => Complex.normSq ((fockBasis Q).repr x A))
  have hnonneg : 0 ≤ ∑ A : {A : Finset (Fin (Q + 1)) // ¬i ∈ A},
      Complex.normSq ((fockBasis Q).repr x A.val) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change _ ≤ ∑ A, Complex.normSq ((fockBasis Q).repr x A)
  linarith

theorem fockCoordinates_norm_sq (x : Space Q) :
    ‖fockCoordinates Q x‖ ^ 2 = fockMass x := by
  simp only [EuclideanSpace.norm_sq_eq, fockCoordinates_apply,
    Complex.normSq_eq_norm_sq, fockMass]

theorem fockOperator_norm_le_one (T : Module.End ℂ (Space Q))
    (hT : ∀ x, fockMass (T x) ≤ fockMass x) : ‖fockOperator T‖ ≤ 1 := by
  apply (fockOperator T).opNorm_le_bound zero_le_one
  intro v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  rw [fockOperator_coordinates, one_mul]
  have h := hT x
  rw [← fockCoordinates_norm_sq, ← fockCoordinates_norm_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Actual CAR creators and annihilators are contractions in the
canonical occupation norm, uniformly in the number of spectator modes. -/
theorem fockOperator_create_norm (i : Fin (Q + 1)) :
    ‖fockOperator (create i)‖ ≤ 1 :=
  fockOperator_norm_le_one _ (fockMass_create_le i)

theorem fockOperator_annihilate_norm (i : Fin (Q + 1)) :
    ‖fockOperator (annihilate i)‖ ≤ 1 :=
  fockOperator_norm_le_one _ (fockMass_annihilate_le i)

theorem fockOperator_create_adjoint (i : Fin (Q + 1)) :
    (fockOperator (create i)).adjoint = fockOperator (annihilate i) := by
  have h : fockOperator (create i) = (fockOperator (annihilate i)).adjoint := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro u v
    obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective u
    obtain ⟨y, rfl⟩ := (fockCoordinates Q).surjective v
    simp only [fockOperator_coordinates, PiLp.inner_apply, RCLike.inner_apply',
      fockCoordinates_apply]
    exact fock_inner_create_annihilate i x y
  simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg
    ContinuousLinearMap.adjoint h

theorem fockOperator_sum {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (Space Q)) :
    fockOperator (∑ i ∈ s, T i) = ∑ i ∈ s, fockOperator (T i) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, sum_apply,
    LinearMap.sum_apply, map_sum]

theorem fockOperator_transfer_norm (i j : Fin (Q + 1)) :
    ‖fockOperator (transfer i j)‖ ≤ 1 := by
  rw [transfer, fockOperator_mul]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (fockOperator_create_norm i) (fockOperator_annihilate_norm j)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem fockOperator_bondTransfer_norm (i j : Fin (Q + 1)) :
    ‖fockOperator (bondTransfer i j)‖ ≤ 2 := by
  rw [bondTransfer, fockOperator_add]
  calc
    _ ≤ ‖fockOperator (transfer i j)‖ + ‖fockOperator (transfer j i)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (fockOperator_transfer_norm i j) (fockOperator_transfer_norm j i)
    _ = 2 := by norm_num

theorem fockOperator_siteHopping_norm (m : ℕ) (i j : Fin (m + 1)) :
    ‖fockOperator (siteHopping m i j)‖ ≤ 4 := by
  change ‖fockOperator (_ + _)‖ ≤ _
  rw [fockOperator_add]
  calc
    _ ≤ ‖fockOperator (bondTransfer (siteMode m i 0) (siteMode m j 0))‖ +
        ‖fockOperator (bondTransfer (siteMode m i 1) (siteMode m j 1))‖ := norm_add_le _ _
    _ ≤ 2 + 2 := add_le_add
      (fockOperator_bondTransfer_norm (siteMode m i 0) (siteMode m j 0))
      (fockOperator_bondTransfer_norm (siteMode m i 1) (siteMode m j 1))
    _ = 4 := by norm_num

/-- The actual global hopping has an edge-sum bound, independent of
the exponentially large Fock-space dimension. -/
theorem fockOperator_graphHopping_norm {Edge : Type*} [Fintype Edge]
    (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) :
    ‖fockOperator (graphHopping m left right t)‖ ≤ 4 * ∑ e, ‖t e‖ := by
  unfold graphHopping
  rw [fockOperator_sum]
  simp only [fockOperator_smul]
  calc
    _ ≤ ∑ e, ‖t e • fockOperator (siteHopping m (left e) (right e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, ‖t e‖ * 4 := Finset.sum_le_sum fun e _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (fockOperator_siteHopping_norm m (left e) (right e)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem fockOperator_annihilate_adjoint (i : Fin (Q + 1)) :
    (fockOperator (annihilate i)).adjoint = fockOperator (create i) := by
  rw [← fockOperator_create_adjoint, ContinuousLinearMap.adjoint_adjoint]

theorem fockOperator_transfer_adjoint (i j : Fin (Q + 1)) :
    (fockOperator (transfer i j)).adjoint = fockOperator (transfer j i) := by
  simp only [transfer, fockOperator_mul, ContinuousLinearMap.adjoint_comp,
    fockOperator_create_adjoint, fockOperator_annihilate_adjoint]

theorem fockOperator_bondTransfer_adjoint (i j : Fin (Q + 1)) :
    (fockOperator (bondTransfer i j)).adjoint = fockOperator (bondTransfer i j) := by
  simp only [bondTransfer, fockOperator_add, map_add,
    fockOperator_transfer_adjoint, add_comm]

theorem fockOperator_siteHopping_adjoint (m : ℕ) (i j : Fin (m + 1)) :
    (fockOperator (siteHopping m i j)).adjoint = fockOperator (siteHopping m i j) := by
  change (fockOperator (_ + _)).adjoint = fockOperator (_ + _)
  simp only [fockOperator_add, map_add, fockOperator_bondTransfer_adjoint]

theorem fockOperator_graphHopping_adjoint {Edge : Type*} [Fintype Edge]
    (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    (fockOperator (graphHopping m left right (fun e => (t e : ℂ)))).adjoint =
      fockOperator (graphHopping m left right (fun e => (t e : ℂ))) := by
  unfold graphHopping
  rw [fockOperator_sum]
  simp only [fockOperator_smul, map_sum, map_smulₛₗ,
    fockOperator_siteHopping_adjoint, Complex.conj_ofReal]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HalfFilledSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual half-filled occupation basis splits into spins and charge defects. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

theorem spinOccupationSet_mem (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i : Fin (m + 1)) (σ : Fin 2) :
    siteMode m i σ ∈ spinOccupationSet m s ↔ σ = s i := by
  change siteMode m i σ ∈
    (Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s) :
      Finset (Fin ((2 * m + 1) + 1))) ↔ _
  rw [Set.powersetCard.mem_coe_iff,
    Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  constructor
  · rintro ⟨j, hj⟩
    have h := (siteMode_eq_iff m j i (s j) σ).mp hj
    simpa only [h.1] using h.2.symm
  · intro h
    exact ⟨i, congrArg (siteMode m i) h.symm⟩

theorem spinOccupationSet_card (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    (spinOccupationSet m s).card = m + 1 :=
  (Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)).property

theorem occupationAt_spinOccupationSet (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i : Fin (m + 1)) : occupationAt m (spinOccupationSet m s) i = 1 := by
  apply Fin.ext
  simp only [occupationAt, spinOccupationSet_mem]
  generalize s i = σ
  fin_cases σ <;> norm_num

/-- The sum of actual local particle counts is the cardinality of the
occupied-mode set, including doubly occupied sites. -/
theorem occupationAt_sum (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    (∑ i, (occupationAt m A i : ℕ)) = A.card := by
  have hlocal (i : Fin (m + 1)) :
      (occupationAt m A i : ℕ) = ∑ σ : Fin 2,
        if siteMode m i σ ∈ A then 1 else 0 := by
    rw [Fin.sum_univ_two]
    rfl
  simp_rw [hlocal]
  rw [← Fintype.sum_prod_type (fun p : Fin (m + 1) × Fin 2 =>
    if siteMode m p.1 p.2 ∈ A then (1 : ℕ) else 0)]
  have h := (siteModes m).sum_comp
    (fun k => if k ∈ A then (1 : ℕ) else 0)
  change (∑ p : Fin (m + 1) × Fin 2,
      if siteModes m p ∈ A then 1 else 0) = A.card
  rw [h]
  simp

theorem onePerSite_mem_iff (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1)))
    (hA : ∀ i, occupationAt m A i = 1) (i : Fin (m + 1)) (σ : Fin 2) :
    siteMode m i σ ∈ A ↔ σ = occupationSpin m A i := by
  have hi := congrArg Fin.val (hA i)
  change (if siteMode m i 0 ∈ A then 1 else 0) +
    (if siteMode m i 1 ∈ A then 1 else 0) = 1 at hi
  fin_cases σ <;> dsimp [occupationSpin] <;> split_ifs at * <;> simp_all

/-- Every one-electron-per-site occupation is a unique canonical spin
occupation; there are no missing states in the low sector. -/
theorem onePerSite_eq_spinOccupationSet (m : ℕ)
    (A : Finset (Fin ((2 * m + 1) + 1))) (hA : ∀ i, occupationAt m A i = 1) :
    A = spinOccupationSet m (occupationSpin m A) := by
  ext k
  obtain ⟨⟨i, σ⟩, rfl⟩ := (siteModes m).surjective k
  exact (onePerSite_mem_iff m A hA i σ).trans (spinOccupationSet_mem m _ i σ).symm

theorem halfFilled_occupation_sum (m : ℕ) (A : HalfFilledBasis m) :
    (∑ i, (occupationAt m A.val i : ℕ)) = m + 1 :=
  (occupationAt_sum m A.val).trans A.property

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_DiagonalPenalty
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The concrete inverse of a charge-sector penalty

The high block of the Hubbard penalty is diagonal in the occupation basis.
That block and its inverse are continuous linear maps satisfying the
positivity, symmetry and inverse-norm hypotheses of the second-order
perturbation theorem.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

variable {Basis : Type*} [Fintype Basis]

theorem diagonalPenalty_form (weight : Basis → ℝ) (x : EuclideanSpace ℂ Basis) :
    ⟪x, diagonalPenalty weight x⟫_ℝ = ∑ s, weight s * ‖x s‖ ^ 2 := by
  simp only [PiLp.inner_apply, diagonalPenalty_apply,
    real_inner_smul_right, real_inner_self_eq_norm_sq]

theorem diagonalPenalty_symmetric (weight : Basis → ℝ)
    (x y : EuclideanSpace ℂ Basis) :
    ⟪x, diagonalPenalty weight y⟫_ℝ = ⟪diagonalPenalty weight x, y⟫_ℝ := by
  simp only [PiLp.inner_apply, diagonalPenalty_apply,
    real_inner_smul_right, real_inner_smul_left]

theorem diagonalPenalty_gap (weight : Basis → ℝ) (g : ℝ)
    (hgap : ∀ s, g ≤ weight s) (x : EuclideanSpace ℂ Basis) :
    g * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty weight x⟫_ℝ := by
  rw [diagonalPenalty_form, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hgap s) (sq_nonneg _)

theorem diagonalPenalty_norm_le (weight : Basis → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hweight : ∀ s, |weight s| ≤ C) :
    ‖diagonalPenalty weight‖ ≤ C := by
  apply (diagonalPenalty weight).opNorm_le_bound hC
  intro x
  have hsq : ‖diagonalPenalty weight x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    have hw : weight s ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 (hweight s)
    simpa only [diagonalPenalty_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using
      mul_le_mul_of_nonneg_right hw (sq_nonneg ‖x s‖)
  have hn := norm_nonneg (diagonalPenalty weight x)
  have hcx : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith

theorem diagonalPenalty_inverse_right (weight : Basis → ℝ)
    (hweight : ∀ s, weight s ≠ 0) (x : EuclideanSpace ℂ Basis) :
    diagonalPenalty weight (diagonalPenalty (fun s => (weight s)⁻¹) x) = x := by
  ext s
  simp [hweight s]

theorem diagonalPenalty_inverse_norm {g : ℝ} (hg : 0 < g) (weight : Basis → ℝ)
    (hgap : ∀ s, g ≤ weight s) :
    ‖diagonalPenalty (fun s => (weight s)⁻¹)‖ ≤ 1 / g := by
  apply diagonalPenalty_norm_le _ (by positivity)
  intro s
  have hw : 0 < weight s := hg.trans_le (hgap s)
  rw [abs_of_pos (inv_pos.mpr hw)]
  simpa only [one_div] using one_div_le_one_div_of_le hg (hgap s)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Perturbation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Second-order block estimates

The finite reductions use the bottom-energy estimate from the binary
manuscript's `lem:second-order` and the unit manuscript's `lem:perturbation`.
Explicit positivity and operator norm bounds give vector and variational
estimates for the penalty, inverse, coupling and high perturbation blocks.

Real inner products also express the real quadratic forms of complex spin
Hilbert spaces by restriction of scalars.
-/

noncomputable section

open scoped InnerProductSpace

namespace ContinuumCoulomb
namespace Perturbation

variable {L H : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℝ L]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem inverseForm_nonneg (A T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x) (hA : ∀ q, 0 ≤ penaltyForm A q) (p : L) :
    0 ≤ inverseForm T B p := by
  have h := hA (T (B p))
  simpa only [penaltyForm, hAT, real_inner_comm, inverseForm] using h

/-- The precise square-completion identity, before any estimates. -/
theorem penalty_square_identity (A T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (p : L) (q : H) {σ : ℝ} (hσ : σ ≠ 0) :
    σ * penaltyForm A q + 2 * ⟪q, B p⟫_ℝ =
      σ * penaltyForm A (q + σ⁻¹ • T (B p)) - σ⁻¹ * inverseForm T B p := by
  have hcross : ⟪T (B p), A q⟫_ℝ = ⟪q, B p⟫_ℝ := by
    rw [hAsymm, hAT, real_inner_comm]
  simp only [penaltyForm, inverseForm, map_add, map_smul, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, hAT, hcross]
  rw [real_inner_comm (T (B p)) (B p)]
  field_simp
  ring

/-- The trial vector used in the second-order variational upper bound. -/
theorem blockEnergy_trial_identity (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x) (p : L) :
    blockEnergy A D B p (-(T (B p))) =
      -inverseForm T B p + ⟪-(T (B p)), D (-(T (B p)))⟫_ℝ := by
  simp only [blockEnergy, penaltyForm, inverseForm, map_neg, hAT,
    inner_neg_left, inner_neg_right]
  rw [real_inner_comm (T (B p)) (B p)]
  ring

theorem inverse_coupling_norm_le (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (_hε : 0 ≤ ε)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (p : L) :
    ‖T (B p)‖ ≤ ε * ‖p‖ := by
  have hBp : ‖B p‖ ≤ ε * g * ‖p‖ :=
    (B.le_opNorm p).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  calc
    ‖T (B p)‖ ≤ ‖T‖ * ‖B p‖ := T.le_opNorm _
    _ ≤ (1 / g) * (ε * g * ‖p‖) := by
      exact mul_le_mul hT hBp (norm_nonneg _) (by positivity)
    _ = ε * ‖p‖ := by field_simp

theorem inverseForm_le (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (p : L) :
    inverseForm T B p ≤ g * ε ^ 2 * ‖p‖ ^ 2 := by
  have hBp : ‖B p‖ ≤ ε * g * ‖p‖ :=
    (B.le_opNorm p).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hTBp := inverse_coupling_norm_le T B hg hε hT hB p
  calc
    inverseForm T B p ≤ ‖B p‖ * ‖T (B p)‖ := real_inner_le_norm _ _
    _ ≤ (ε * g * ‖p‖) * (ε * ‖p‖) :=
      mul_le_mul hBp hTBp (norm_nonneg _) (by positivity)
    _ = g * ε ^ 2 * ‖p‖ ^ 2 := by ring

theorem highPerturbation_abs_le (D : H →L[ℝ] H)
    {g ε : ℝ} (hD : ‖D‖ ≤ ε * g) (q : H) :
    |⟪q, D q⟫_ℝ| ≤ ε * g * ‖q‖ ^ 2 := by
  calc
    |⟪q, D q⟫_ℝ| ≤ ‖q‖ * ‖D q‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖q‖ * (ε * g * ‖q‖) := by
      exact mul_le_mul_of_nonneg_left
        ((D.le_opNorm q).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))
        (norm_nonneg _)
    _ = ε * g * ‖q‖ ^ 2 := by ring

theorem highPerturbation_relative_lower (A D : H →L[ℝ] H)
    {g ε : ℝ} (hε : 0 ≤ ε) (hD : ‖D‖ ≤ ε * g)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q) (q : H) :
    -(ε * penaltyForm A q) ≤ ⟪q, D q⟫_ℝ := by
  have h := (abs_le.mp (highPerturbation_abs_le D hD q)).1
  have hgap' := mul_le_mul_of_nonneg_left (hgap q) hε
  nlinarith

/-- Completing a square lowers the full form by the inverse coupling form. -/
theorem blockEnergy_lower (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hD : ‖D‖ ≤ ε * g) (p : L) (q : H) :
    -inverseForm T B p / (1 - ε) ≤ blockEnergy A D B p q := by
  have hσ : 0 < 1 - ε := by linarith
  have hid := penalty_square_identity A T B hAT hAsymm p q (ne_of_gt hσ)
  have hsquare := mul_nonneg (le_of_lt hσ) (hA (q + (1 - ε)⁻¹ • T (B p)))
  have hDq := highPerturbation_relative_lower A D hε hD hgap q
  unfold blockEnergy
  rw [div_eq_mul_inv]
  nlinarith

/-- Pointwise inverse-form control gives the lower Rayleigh bound. -/
theorem blockRayleigh_lower (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε κ : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hκ : 0 ≤ κ)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hD : ‖D‖ ≤ ε * g)
    (hK : ∀ p, inverseForm T B p ≤ κ * ‖p‖ ^ 2)
    (p : L) (q : H) (hnorm : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2) :
    -κ / (1 - ε) ≤ blockRayleigh A D B p q := by
  have hσ : 0 < 1 - ε := by linarith
  have he := blockEnergy_lower A T D B hε hε1 hAT hAsymm hA hgap hD p q
  have hK' := div_le_div_of_nonneg_right (neg_le_neg (hK p)) (le_of_lt hσ)
  have hq : 0 ≤ κ * (1 - ε)⁻¹ * ‖q‖ ^ 2 := by positivity
  unfold blockRayleigh
  apply (le_div_iff₀ hnorm).mpr
  simp only [div_eq_mul_inv] at he hK' ⊢
  nlinarith

theorem cubic_lower_error {g ε κ : ℝ} (hg : 0 < g)
    (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) (hκ : κ ≤ g * ε ^ 2) :
    -κ - 2 * g * ε ^ 3 ≤ -κ / (1 - ε) := by
  have hσ : 0 < 1 - ε := by linarith
  have hsmall : 0 ≤ g * ε ^ 3 * (1 - 2 * ε) :=
    mul_nonneg (by positivity) (by linarith)
  have hκ' := mul_le_mul_of_nonneg_left hκ hε
  apply (le_div_iff₀ hσ).mpr
  nlinarith

/-- The explicit second-order trial vector gives a cubic upper error. -/
theorem blockRayleigh_trial_upper (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε κ : ℝ} (hg : 0 < g) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hAT : ∀ x, A (T x) = x)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hκ : κ ≤ g * ε ^ 2)
    (p : L) (hp : ‖p‖ = 1) (hattain : inverseForm T B p = κ) :
    blockRayleigh A D B p (-(T (B p))) ≤ -κ + 2 * g * ε ^ 3 := by
  have hnorm : ‖-(T (B p))‖ ≤ ε := by
    simpa only [norm_neg, hp, mul_one] using inverse_coupling_norm_le T B hg hε hT hB p
  have hr : ‖-(T (B p))‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg (-(T (B p)))]
  have hr0 : 0 ≤ ‖-(T (B p))‖ ^ 2 := sq_nonneg _
  have hd := (abs_le.mp (highPerturbation_abs_le D hD (-(T (B p))))).2
  have hd' : ⟪-(T (B p)), D (-(T (B p)))⟫_ℝ ≤ g * ε ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hr (show 0 ≤ ε * g by positivity)
    nlinarith
  have hκr : κ * ‖-(T (B p))‖ ^ 2 ≤ g * ε ^ 4 := by
    have h1 := mul_le_mul_of_nonneg_right hκ hr0
    have h2 := mul_le_mul_of_nonneg_left hr (show 0 ≤ g * ε ^ 2 by positivity)
    nlinarith
  have hε4 : g * ε ^ 4 ≤ g * ε ^ 3 := by
    have h := mul_nonneg (show 0 ≤ g * ε ^ 3 by positivity)
      (show 0 ≤ 1 - ε by linarith)
    nlinarith
  have hden : 0 < 1 + ‖-(T (B p))‖ ^ 2 := by positivity
  unfold blockRayleigh
  rw [blockEnergy_trial_identity A T D B hAT p, hattain, hp, one_pow]
  apply (div_le_iff₀ hden).mpr
  have hcost : 0 ≤ 2 * g * ε ^ 3 * ‖-(T (B p))‖ ^ 2 := by positivity
  nlinarith

/-- Supporting variational second-order estimate for the zero low-low
block case.  The effective positive inverse form is bounded by `κ` and
attains it at the supplied unit vector, exactly as for the maximum
eigenvector of the finite positive matrix `PBA⁻¹BP` in the manuscript. -/
theorem blockBottom_second_order (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε κ : ℝ} (hg : 0 < g) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hK : ∀ p, inverseForm T B p ≤ κ * ‖p‖ ^ 2)
    (p₀ : L) (hp₀ : ‖p₀‖ = 1) (hattain : inverseForm T B p₀ = κ) :
    |blockBottom A D B + κ| ≤ 2 * g * ε ^ 3 := by
  have hκ0 : 0 ≤ κ := by
    rw [← hattain]
    exact inverseForm_nonneg A T B hAT hA p₀
  have hκ : κ ≤ g * ε ^ 2 := by
    have h := inverseForm_le T B hg hε hT hB p₀
    simpa only [hattain, hp₀, one_pow, mul_one] using h
  have hnorm : 0 < ‖p₀‖ ^ 2 + ‖-(T (B p₀))‖ ^ 2 := by rw [hp₀]; positivity
  have hnonempty :
      {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = blockRayleigh A D B p q}.Nonempty :=
    ⟨_, p₀, -(T (B p₀)), hnorm, rfl⟩
  have hlower (e : ℝ)
      (he : ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = blockRayleigh A D B p q) : -κ - 2 * g * ε ^ 3 ≤ e := by
    obtain ⟨p, q, hpq, rfl⟩ := he
    exact (cubic_lower_error hg hε hεhalf hκ).trans
      (blockRayleigh_lower A T D B hε (by linarith) hκ0 hAT hAsymm hA hgap hD hK p q hpq)
  have hbdd : BddBelow
      {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = blockRayleigh A D B p q} := ⟨_, hlower⟩
  have hbottomLower : -κ - 2 * g * ε ^ 3 ≤ blockBottom A D B :=
    le_csInf hnonempty hlower
  have hbottomUpper : blockBottom A D B ≤ -κ + 2 * g * ε ^ 3 :=
    (csInf_le hbdd ⟨p₀, -(T (B p₀)), hnorm, rfl⟩).trans
      (blockRayleigh_trial_upper A T D B hg hε hεhalf hAT hT hB hD hκ p₀ hp₀ hattain)
  apply abs_le.mpr
  constructor <;> linarith

theorem effectiveForm_smul (C : L →L[ℝ] L) (T : H →L[ℝ] H)
    (B : L →L[ℝ] H) (r : ℝ) (p : L) :
    effectiveForm C T B (r • p) = r ^ 2 * effectiveForm C T B p := by
  simp only [effectiveForm, inverseForm, map_smul, real_inner_smul_left,
    real_inner_smul_right]
  ring

/-- Finite dimensionality supplies the effective ground vector; this
is not an additional simulation assumption. -/
theorem effectiveForm_minimizer [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (u : L) (hu : ‖u‖ = 1) :
    ∃ p : L, ‖p‖ = 1 ∧
      ∀ x : L, effectiveForm C T B p * ‖x‖ ^ 2 ≤ effectiveForm C T B x := by
  have := FiniteDimensional.proper_rclike ℝ L
  have hc : Continuous (effectiveForm C T B) :=
    (continuous_id.inner C.continuous).sub
      (B.continuous.inner (T.continuous.comp B.continuous))
  have hnonempty : (Metric.sphere (0 : L) 1).Nonempty := ⟨u, by simpa using hu⟩
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_sphere (0 : L) 1).exists_isMinOn hnonempty hc.continuousOn
  refine ⟨p, by simpa using hp, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, effectiveForm, inverseForm]
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have h := hmin (show (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : L) 1 by simpa using hunit)
  change effectiveForm C T B p ≤ effectiveForm C T B ((‖x‖⁻¹ : ℝ) • x) at h
  rw [effectiveForm_smul] at h
  calc
    effectiveForm C T B p * ‖x‖ ^ 2 ≤
        (‖x‖⁻¹ ^ 2 * effectiveForm C T B x) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = effectiveForm C T B x := by field_simp

theorem effectiveBottom_eq (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (p : L) (hp : ‖p‖ = 1)
    (hmin : ∀ x : L, effectiveForm C T B p * ‖x‖ ^ 2 ≤ effectiveForm C T B x) :
    effectiveBottom C T B = effectiveForm C T B p := by
  have hlower (e : ℝ) (he : ∃ x : L, ‖x‖ = 1 ∧ e = effectiveForm C T B x) :
      effectiveForm C T B p ≤ e := by
    obtain ⟨x, hx, rfl⟩ := he
    simpa only [hx, one_pow, mul_one] using hmin x
  exact le_antisymm (csInf_le ⟨_, hlower⟩ ⟨p, hp, rfl⟩)
    (le_csInf ⟨_, p, hp, rfl⟩ hlower)

/-- The sharper zero-low-block estimate also compares actual variational
infima without a separately supplied effective maximizing vector. -/
theorem finite_blockBottom_second_order [FiniteDimensional ℝ L]
    (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (u : L) (hu : ‖u‖ = 1) :
    |blockBottom A D B - effectiveBottom (0 : L →L[ℝ] L) T B| ≤ 2 * g * ε ^ 3 := by
  obtain ⟨p, hp, hmin⟩ := effectiveForm_minimizer (0 : L →L[ℝ] L) T B u hu
  have hK (x : L) : inverseForm T B x ≤ inverseForm T B p * ‖x‖ ^ 2 := by
    have h := hmin x
    simp only [effectiveForm, zero_apply, inner_zero_right, zero_sub] at h
    nlinarith
  have hvalue := effectiveBottom_eq (0 : L →L[ℝ] L) T B p hp hmin
  simp only [effectiveForm, zero_apply, inner_zero_right, zero_sub] at hvalue
  rw [hvalue, sub_neg_eq_add]
  exact blockBottom_second_order A T D B hg hε hεhalf hAT hAsymm hA hgap
    hT hB hD hK p hp rfl

end Perturbation
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Second-order estimate with the global charge penalty

The occupation configurations determine the penalty, its inverse, its
positivity and its spectral gap. The resulting bottom-energy comparison
retains every electron and spin configuration.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

theorem hubbardLowUnit_norm (m : ℕ) : ‖hubbardLowUnit m‖ = 1 := by
  simp [hubbardLowUnit, PiLp.norm_single]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockBlocks
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete hopping blocks on the actual half-filled Fock basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

section Coordinates
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem coordinateInclusion_single [DecidableEq α] [DecidableEq β] (f : α → β) (a : α) :
    coordinateInclusion f (EuclideanSpace.single a (1 : ℂ)) =
      EuclideanSpace.single (f a) (1 : ℂ) := by
  classical
  simp [coordinateInclusion, coordinateInclusionLinear, PiLp.single_apply]
  ext b
  simp [PiLp.single_apply]

theorem coordinateInclusion_norm_le (f : α → β) (hf : Function.Injective f) :
    ‖coordinateInclusion f‖ ≤ 1 := by
  apply (coordinateInclusion f).opNorm_le_bound zero_le_one
  intro x
  rw [coordinateInclusion_norm_map f hf, one_mul]

@[simp] theorem coordinateRestriction_apply (f : α → β)
    (x : EuclideanSpace ℂ β) (a : α) : coordinateRestriction f x a = x (f a) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right (coordinateInclusion f)
    (EuclideanSpace.single a (1 : ℂ)) x
  rw [coordinateInclusion_single, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left] at h
  simpa only [coordinateRestriction, map_one, one_mul] using h

theorem coordinateRestriction_norm_le (f : α → β) (hf : Function.Injective f) :
    ‖coordinateRestriction f‖ ≤ 1 := by
  change ‖(coordinateInclusion f).adjoint‖ ≤ 1
  rw [LinearIsometryEquiv.norm_map]
  exact coordinateInclusion_norm_le f hf

theorem coordinateCompression_norm (R : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ γ)
    (T : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (I : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (hR : ‖R‖ ≤ 1) (hI : ‖I‖ ≤ 1) : ‖R.comp (T.comp I)‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖R‖ * ‖T.comp I‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul hR
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hI (norm_nonneg _))) (norm_nonneg _) zero_le_one
    _ = _ := by ring

end Coordinates

theorem highOccupationIndex_injective (m : ℕ) : Function.Injective (highOccupationIndex m) := by
  intro A B h
  apply Subtype.ext
  exact Subtype.ext h

theorem lowFockInclusion_norm (m : ℕ) : ‖lowFockInclusion m‖ ≤ 1 :=
  coordinateInclusion_norm_le _ (spinOccupationSet_injective m)

theorem highFockInclusion_norm (m : ℕ) : ‖highFockInclusion m‖ ≤ 1 :=
  coordinateInclusion_norm_le _ (highOccupationIndex_injective m)

theorem highFockRestriction_norm (m : ℕ) : ‖highFockRestriction m‖ ≤ 1 :=
  coordinateRestriction_norm_le _ (highOccupationIndex_injective m)

variable {Edge : Type*} [Fintype Edge]

theorem actualHubbardCoupling_norm (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    ‖actualHubbardCoupling m left right t‖ ≤ 4 * ∑ e, |t e| := by
  unfold actualHubbardCoupling
  rw [ContinuousLinearMap.norm_restrictScalars]
  have hgraph : ‖fockOperator (graphHopping m left right (fun e => (t e : ℂ)))‖ ≤
      4 * ∑ e, |t e| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      fockOperator_graphHopping_norm m left right (fun e => (t e : ℂ))
  exact (coordinateCompression_norm _ _ _ (highFockRestriction_norm m)
    (lowFockInclusion_norm m)).trans hgraph

theorem actualHubbardHighHopping_norm (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    ‖actualHubbardHighHopping m left right t‖ ≤ 4 * ∑ e, |t e| := by
  unfold actualHubbardHighHopping
  rw [ContinuousLinearMap.norm_restrictScalars]
  have hgraph : ‖fockOperator (graphHopping m left right (fun e => (t e : ℂ)))‖ ≤
      4 * ∑ e, |t e| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      fockOperator_graphHopping_norm m left right (fun e => (t e : ℂ))
  exact (coordinateCompression_norm _ _ _ (highFockRestriction_norm m)
    (highFockInclusion_norm m)).trans hgraph

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-particle support and the true low/high Fock projections. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

variable {Q : ℕ}

theorem totalNumber_basis (A : Finset (Fin (Q + 1))) :
    totalNumber Q (fockBasis Q A) = (A.card : ℂ) • fockBasis Q A := by
  simp only [totalNumber, LinearMap.sum_apply, number_basis]
  have hpoint (i : Fin (Q + 1)) :
      (if i ∈ A then fockBasis Q A else 0) =
        (if i ∈ A then (1 : ℂ) else 0) • fockBasis Q A := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_smul]
  simp

theorem totalNumber_eq_diagonal (Q : ℕ) :
    totalNumber Q = fockDiagonal (fun A => (A.card : ℂ)) := by
  apply (fockBasis Q).ext
  intro A
  rw [totalNumber_basis, fockDiagonal_basis]

theorem totalNumber_eigen_coordinate_zero (N : ℕ) (x : Space Q)
    (hx : totalNumber Q x = (N : ℂ) • x) (A : Finset (Fin (Q + 1)))
    (hA : A.card ≠ N) : (fockBasis Q).repr x A = 0 := by
  have h := congrArg (fun y => (fockBasis Q).repr y A) hx
  rw [totalNumber_eq_diagonal, fockDiagonal_coordinate, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at h
  have hne : (A.card : ℂ) ≠ (N : ℂ) := by exact_mod_cast hA
  have hz : ((A.card : ℂ) - N) * (fockBasis Q).repr x A = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

theorem isHalfFilled_of_totalNumber (m : ℕ) (x : Space (2 * m + 1))
    (hx : totalNumber (2 * m + 1) x = ((m + 1 : ℕ) : ℂ) • x) : IsHalfFilled m x :=
  totalNumber_eigen_coordinate_zero (m + 1) x hx

theorem totalNumber_spinWedge (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    totalNumber (2 * m + 1) (spinWedge m s) =
      ((m + 1 : ℕ) : ℂ) • spinWedge m s := by
  rw [spinWedge_eq_fockBasis, totalNumber_basis, spinOccupationSet_card]

theorem totalNumber_spinEmbedding (m : ℕ) (u : SourceSpinVector (m + 1)) :
    totalNumber (2 * m + 1) (spinEmbedding m u) =
      ((m + 1 : ℕ) : ℂ) • spinEmbedding m u := by
  change totalNumber (2 * m + 1) (∑ s, u s • spinWedge m s) =
    ((m + 1 : ℕ) : ℂ) • ∑ s, u s • spinWedge m s
  rw [map_sum]
  simp_rw [map_smul, totalNumber_spinWedge]
  simp only [Finset.smul_sum, smul_smul, mul_comm]

theorem spinOccupationSet_range_iff (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    (∃ s, spinOccupationSet m s = A) ↔ ∀ i, occupationAt m A i = 1 := by
  constructor
  · rintro ⟨s, rfl⟩
    exact occupationAt_spinOccupationSet m s
  · intro hA
    exact ⟨occupationSpin m A, (onePerSite_eq_spinOccupationSet m A hA).symm⟩

theorem highOccupationIndex_range_iff (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    (∃ B, highOccupationIndex m B = A) ↔
      A.card = m + 1 ∧ ¬ ∀ i, occupationAt m A i = 1 := by
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B.val.property, B.property⟩
  · rintro ⟨hcard, hdefect⟩
    exact ⟨⟨⟨A, hcard⟩, hdefect⟩, rfl⟩

theorem coordinateInclusion_restriction_apply {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (x : EuclideanSpace ℂ β) (b : β) :
    coordinateInclusion f (coordinateRestriction f x) b =
      if ∃ a, f a = b then x b else 0 := by
  classical
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [coordinateInclusion_apply_image f hf, coordinateRestriction_apply]
    simp
  · rw [ite_eq_right hb]
    exact coordinateInclusion_apply_outside f _ b (by simpa using hb)

theorem lowFock_projector_coordinates (m : ℕ) (x : Space (2 * m + 1)) :
    lowFockInclusion m (lowFockRestriction m (fockCoordinates (2 * m + 1) x)) =
      fockCoordinates (2 * m + 1) (lowProjection m x) := by
  ext A
  change coordinateInclusion _ (coordinateRestriction _ _) A = _
  rw [coordinateInclusion_restriction_apply _ (spinOccupationSet_injective m)]
  simp only [spinOccupationSet_range_iff, fockCoordinates_apply,
    lowProjection, occupationDiagonal, fockDiagonal_coordinate]
  split_ifs <;> simp

theorem highFock_projector_coordinates (m : ℕ) (x : Space (2 * m + 1)) :
    highFockInclusion m (highFockRestriction m (fockCoordinates (2 * m + 1) x)) =
      fockCoordinates (2 * m + 1) (highProjection m x) := by
  ext A
  change coordinateInclusion _ (coordinateRestriction _ _) A = _
  rw [coordinateInclusion_restriction_apply _ (highOccupationIndex_injective m)]
  simp only [highOccupationIndex_range_iff, fockCoordinates_apply,
    highProjection, fockDiagonal_coordinate]
  split_ifs <;> simp

theorem highProjection_of_halfFilled_lowZero (m : ℕ) (x : Space (2 * m + 1))
    (hfill : IsHalfFilled m x) (hlow : lowProjection m x = 0) : highProjection m x = x := by
  apply (fockBasis (2 * m + 1)).repr.injective
  ext A
  rw [highProjection, fockDiagonal_coordinate]
  by_cases hcard : A.card = m + 1
  · by_cases hspin : ∀ i, occupationAt m A i = 1
    · have h := congrArg (fun y => (fockBasis (2 * m + 1)).repr y A) hlow
      simp [lowProjection, occupationDiagonal, fockDiagonal_coordinate, hspin] at h
      simp [hspin, h]
    · simp [hcard, hspin]
  · simp [hcard, hfill A hcard]

theorem lowProjection_transfer_spinWedge_zero (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j : Fin (m + 1)) (hij : i ≠ j) (σ τ : Fin 2) :
    lowProjection m (transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s)) = 0 := by
  apply lowProjection_eq_zero_of_numberEigen m i _ _
    (siteNumber_transfer_eigen m i i j σ τ _ _ (siteNumber_spinWedge m s i))
  norm_num [chargeShift, hij]

theorem lowProjection_siteHopping_spinWedge_zero (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    lowProjection m (siteHopping m i j (spinWedge m s)) = 0 := by
  simp only [siteHopping, twoSiteHopping, bondTransfer, LinearMap.add_apply, map_add,
    lowProjection_transfer_spinWedge_zero m s i j hij,
    lowProjection_transfer_spinWedge_zero m s j i (Ne.symm hij), add_zero]

variable {Edge : Type*} [Fintype Edge]

theorem totalNumber_commute_siteHopping (m : ℕ) (i j : Fin (m + 1)) :
    Commute (totalNumber (2 * m + 1)) (siteHopping m i j) := by
  exact ((totalNumber_commute_transfer _ _).add_right
    (totalNumber_commute_transfer _ _)).add_right
      ((totalNumber_commute_transfer _ _).add_right (totalNumber_commute_transfer _ _))

theorem totalNumber_commute_graphHopping (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) :
    Commute (totalNumber (2 * m + 1)) (graphHopping m left right t) := by
  apply Commute.sum_right
  intro e _
  exact (totalNumber_commute_siteHopping m (left e) (right e)).smul_right (t e)

theorem graphHopping_preserves_halfFilling (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) (x : Space (2 * m + 1))
    (hx : totalNumber (2 * m + 1) x = ((m + 1 : ℕ) : ℂ) • x) :
    IsHalfFilled m (graphHopping m left right t x) := by
  apply isHalfFilled_of_totalNumber
  have h := LinearMap.congr_fun (totalNumber_commute_graphHopping m left right t).eq x
  change totalNumber (2 * m + 1) (graphHopping m left right t x) =
    graphHopping m left right t (totalNumber (2 * m + 1) x) at h
  rw [hx, map_smul] at h
  exact h

theorem lowProjection_graphHopping_spinEmbedding_zero (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e) (u : SourceSpinVector (m + 1)) :
    lowProjection m (graphHopping m left right t (spinEmbedding m u)) = 0 := by
  change lowProjection m (graphHopping m left right t (∑ s, u s • spinWedge m s)) = _
  simp only [graphHopping, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [lowProjection_siteHopping_spinWedge_zero m _ _ _ (hloop _),
    smul_zero, Finset.sum_const_zero]

/-- A true hop from an arbitrary spin state lies entirely in the actual
half-filled charge-defect space. -/
theorem highProjection_graphHopping_spinEmbedding (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e) (u : SourceSpinVector (m + 1)) :
    highProjection m (graphHopping m left right t (spinEmbedding m u)) =
      graphHopping m left right t (spinEmbedding m u) :=
  highProjection_of_halfFilled_lowZero m _
    (graphHopping_preserves_halfFilling m left right t _ (totalNumber_spinEmbedding m u))
    (lowProjection_graphHopping_spinEmbedding_zero m left right t hloop u)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SuperexchangeSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spectral identification of the global Hubbard inverse term. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Edge : Type*} [Fintype Edge]

theorem graphHeisenbergFock_spinEmbedding (m : ℕ)
    (left right : Edge → Fin (m + 1)) (J : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e) (u : SourceSpinVector (m + 1)) :
    graphHeisenbergFock m left right J (spinEmbedding m u) =
      spinEmbedding m (graphSourceAction m left right J u) := by
  simp only [graphHeisenbergFock, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply,
    spinEmbedding_heisenberg m u _ _ (hloop _), ← map_sub, ← map_smul, ← map_sum]
  congr 1
  ext s
  simp [graphSourceAction]

/-- The checked basis compression extends to every entangled spin state. -/
theorem graphSuperexchange_spinEmbedding (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * ((U - V (left e) (right e) : ℝ) : ℂ))
    (u : SourceSpinVector (m + 1)) :
    -(lowProjection m (graphHopping m left right t
      (chargeInverse m U V (graphHopping m left right t (spinEmbedding m u))))) =
        spinEmbedding m (graphSourceAction m left right J u) := by
  let K : Module.End ℂ (Space (2 * m + 1)) :=
    -(lowProjection m * graphHopping m left right t * chargeInverse m U V *
      graphHopping m left right t)
  have hbasis (s : SourceSpinBasis (m + 1)) :
      K (spinWedge m s) = graphHeisenbergFock m left right J (spinWedge m s) := by
    simpa only [K, Module.End.mul_apply, LinearMap.neg_apply, graphHeisenbergFock,
      LinearMap.sum_apply, LinearMap.smul_apply] using
      graphSuperexchange_calibrated m U V hsymm hdiag left right t J
        hloop hsimple hgap hcal s
  have h : K (spinEmbedding m u) =
      graphHeisenbergFock m left right J (spinEmbedding m u) := by
    change K (∑ s, u s • spinWedge m s) =
      graphHeisenbergFock m left right J (∑ s, u s • spinWedge m s)
    simp only [map_sum, map_smul, hbasis]
  exact h.trans (graphHeisenbergFock_spinEmbedding m left right J hloop u)

theorem lowFockInclusion_spinEmbedding (m : ℕ) (p : ActualHubbardLowSpace m) :
    lowFockInclusion m p = fockCoordinates (2 * m + 1) (spinEmbedding m (fun s => p s)) := by
  ext A
  by_cases hA : ∃ s, spinOccupationSet m s = A
  · obtain ⟨s, rfl⟩ := hA
    rw [fockCoordinates_apply, spinEmbedding_coordinate]
    exact coordinateInclusion_apply_image _ (spinOccupationSet_injective m) p s
  · rw [fockCoordinates_apply,
      spinEmbedding_coordinate_outside m _ A (by simpa using hA)]
    exact coordinateInclusion_apply_outside _ p A (by simpa using hA)

theorem lowFockRestriction_inclusion (m : ℕ) (p : ActualHubbardLowSpace m) :
    lowFockRestriction m (lowFockInclusion m p) = p := by
  ext s
  change coordinateRestriction (spinOccupationSet m) (lowFockInclusion m p) s = p s
  rw [coordinateRestriction_apply]
  exact coordinateInclusion_apply_image _ (spinOccupationSet_injective m) p s

theorem lowFockInclusion_injective (m : ℕ) : Function.Injective (lowFockInclusion m) := by
  intro p q h
  simpa only [lowFockRestriction_inclusion] using congrArg (lowFockRestriction m) h

theorem fockOperator_diagonal_apply {Q : ℕ} (f : Finset (Fin (Q + 1)) → ℂ)
    (x : FockCoordinateSpace Q) (A : Finset (Fin (Q + 1))) :
    fockOperator (fockDiagonal f) x A = f A * x A := by
  obtain ⟨y, rfl⟩ := (fockCoordinates Q).surjective x
  rw [fockOperator_coordinates, fockCoordinates_apply, fockDiagonal_coordinate,
    fockCoordinates_apply]

theorem highFockInclusion_chargeInverse (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ) (q : ActualHubbardHighSpace m) :
    highFockInclusion m (actualChargeInverse m U V q) =
      fockOperator (chargeInverse m U V) (highFockInclusion m q) := by
  ext A
  rw [chargeInverse, occupationDiagonal, fockOperator_diagonal_apply]
  change coordinateInclusion (highOccupationIndex m) (actualChargeInverse m U V q) A =
    _ * coordinateInclusion (highOccupationIndex m) q A
  by_cases hA : ∃ B, highOccupationIndex m B = A
  · obtain ⟨B, rfl⟩ := hA
    rw [coordinateInclusion_apply_image _ (highOccupationIndex_injective m),
      coordinateInclusion_apply_image _ (highOccupationIndex_injective m)]
    rfl
  · rw [coordinateInclusion_apply_outside _ _ A (by simpa using hA),
      coordinateInclusion_apply_outside _ _ A (by simpa using hA), mul_zero]

/-- The inverse on the concrete high block is the same actual
occupation-diagonal inverse used in the global CAR compression. -/
theorem actualChargeInverse_coupling_inclusion (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e) (p : ActualHubbardLowSpace m) :
    highFockInclusion m (actualChargeInverse m U V (actualHubbardCoupling m left right t p)) =
      fockCoordinates (2 * m + 1)
        (chargeInverse m U V (graphHopping m left right (fun e => (t e : ℂ))
          (spinEmbedding m (fun s => p s)))) := by
  rw [highFockInclusion_chargeInverse]
  simp only [actualHubbardCoupling, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.comp_apply]
  rw [lowFockInclusion_spinEmbedding, fockOperator_coordinates,
    highFock_projector_coordinates, highProjection_graphHopping_spinEmbedding m _ _ _ hloop,
    fockOperator_coordinates]

theorem graphSourceForm_expectation (m : ℕ)
    (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    (u : SourceSpinVector (m + 1)) :
    graphSourceForm m left right J u =
      (∑ s, star (u s) * graphSourceAction m left right (fun e => (J e : ℂ)) u s).re := by
  have hpoint (e : Edge) (s : SourceSpinBasis (m + 1)) :
      (star (u s) * ((J e : ℂ) *
        (sourceHeisenbergAction (left e) (right e) u s - u s))).re =
      J e * ((star (u s) * sourceHeisenbergAction (left e) (right e) u s).re -
        Complex.normSq (u s)) := by
    simp [Complex.mul_re, Complex.normSq_apply]
    ring
  simp only [graphSourceForm, graphSourceAction, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  simp_rw [hpoint]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rfl

theorem lowFockRestriction_superexchange (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * ((U - V (left e) (right e) : ℝ) : ℂ))
    (u : SourceSpinVector (m + 1)) :
    lowFockRestriction m (fockCoordinates (2 * m + 1)
      (-(graphHopping m left right t
        (chargeInverse m U V (graphHopping m left right t (spinEmbedding m u)))))) =
      WithLp.toLp 2 (graphSourceAction m left right J u) := by
  apply lowFockInclusion_injective m
  rw [lowFock_projector_coordinates, map_neg,
    graphSuperexchange_spinEmbedding m U V hsymm hdiag left right t J
      hloop hsimple hgap hcal, lowFockInclusion_spinEmbedding]

/-- The effective quadratic form of the actual Hubbard blocks is
the entire graph Heisenberg form, with the exact scalar offset. -/
theorem actualHubbard_effectiveForm (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * (U - V (left e) (right e)))
    (p : ActualHubbardLowSpace m) :
    Perturbation.effectiveForm
        (0 : ActualHubbardLowSpace m →L[ℝ] ActualHubbardLowSpace m)
        (actualChargeInverse m U V) (actualHubbardCoupling m left right t) p =
      graphSourceForm m left right J (fun s => p s) := by
  let A := graphHopping m left right (fun e => (t e : ℂ))
  let x := spinEmbedding m (fun s => p s)
  let B := actualHubbardCoupling m left right t
  let T := actualChargeInverse m U V
  have hH : fockOperator A (lowFockInclusion m p) = fockCoordinates (2 * m + 1) (A x) := by
    rw [lowFockInclusion_spinEmbedding, fockOperator_coordinates]
  have hBp : B p = highFockRestriction m (fockCoordinates (2 * m + 1) (A x)) := by
    change highFockRestriction m (fockOperator A (lowFockInclusion m p)) = _
    rw [hH]
  have hinv : highFockInclusion m (T (B p)) =
      fockCoordinates (2 * m + 1) (chargeInverse m U V (A x)) :=
    actualChargeInverse_coupling_inclusion m U V left right t hloop p
  have hinner : ⟪B p, T (B p)⟫_ℂ =
      ⟪lowFockInclusion m p,
        fockCoordinates (2 * m + 1) (A (chargeInverse m U V (A x)))⟫_ℂ := by
    calc
      _ = ⟪fockCoordinates (2 * m + 1) (A x), highFockInclusion m (T (B p))⟫_ℂ := by
        rw [hBp]
        exact ContinuousLinearMap.adjoint_inner_left (highFockInclusion m) _ _
      _ = ⟪fockCoordinates (2 * m + 1) (A x),
          fockCoordinates (2 * m + 1) (chargeInverse m U V (A x))⟫_ℂ := by rw [hinv]
      _ = _ := by
        have h := ContinuousLinearMap.adjoint_inner_left (fockOperator A)
          (fockCoordinates (2 * m + 1) (chargeInverse m U V (A x))) (lowFockInclusion m p)
        rw [fockOperator_graphHopping_adjoint, hH, fockOperator_coordinates] at h
        exact h
  have hcalC (e : Edge) : (t e : ℂ) ^ 2 =
      (J e : ℂ) * ((U - V (left e) (right e) : ℝ) : ℂ) := by exact_mod_cast hcal e
  have hcompress := lowFockRestriction_superexchange m U V hsymm hdiag left right
    (fun e => (t e : ℂ)) (fun e => (J e : ℂ)) hloop hsimple hgap hcalC (fun s => p s)
  have heffective : -(⟪B p, T (B p)⟫_ℂ) =
      ⟪p, WithLp.toLp 2 (graphSourceAction m left right (fun e => (J e : ℂ)) (fun s => p s))⟫_ℂ := by
    rw [hinner]
    have h := ContinuousLinearMap.adjoint_inner_right (lowFockInclusion m) p
      (fockCoordinates (2 * m + 1) (-(A (chargeInverse m U V (A x)))))
    change ⟪p, lowFockRestriction m _⟫_ℂ = _ at h
    rw [hcompress, map_neg, inner_neg_right] at h
    exact h.symm
  calc
    _ = -⟪B p, T (B p)⟫_ℝ := by
      simp only [Perturbation.effectiveForm, Perturbation.inverseForm,
        zero_apply, inner_zero_right, zero_sub]
      rfl
    _ = (⟪p, WithLp.toLp 2
        (graphSourceAction m left right (fun e => (J e : ℂ)) (fun s => p s))⟫_ℂ).re := by
      have hreal : ⟪B p, T (B p)⟫_ℝ = (⟪B p, T (B p)⟫_ℂ).re := by
        simp only [PiLp.inner_apply, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro s _
        rfl
      rw [hreal]
      exact congrArg Complex.re heffective
    _ = _ := by
      rw [graphSourceForm_expectation]
      simp only [PiLp.inner_apply, RCLike.inner_apply']
      rfl

theorem sourceSpinMass_euclidean (m : ℕ) (p : ActualHubbardLowSpace m) :
    sourceSpinMass (fun s => p s) = ‖p‖ ^ 2 := by
  simp only [sourceSpinMass, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

/-- Equality of the two actual variational bottoms; no minimizer or
assertion about the desired source energy is supplied as an assumption. -/
theorem actualHubbard_effectiveBottom (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * (U - V (left e) (right e))) :
    Perturbation.effectiveBottom
        (0 : ActualHubbardLowSpace m →L[ℝ] ActualHubbardLowSpace m)
        (actualChargeInverse m U V) (actualHubbardCoupling m left right t) =
      graphSourceBottom m left right J := by
  unfold Perturbation.effectiveBottom graphSourceBottom
  congr 1
  ext e
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun s => p s, ?_, ?_⟩
    · rw [sourceSpinMass_euclidean, hp]
      norm_num
    · exact actualHubbard_effectiveForm m U V hsymm hdiag left right t J
        hloop hsimple hgap hcal p
  · rintro ⟨u, hu, rfl⟩
    let p : ActualHubbardLowSpace m := WithLp.toLp 2 u
    have hp : ‖p‖ = 1 := by
      have hsq : ‖p‖ ^ 2 = 1 := (sourceSpinMass_euclidean m p).symm.trans hu
      nlinarith [norm_nonneg p]
    refine ⟨p, hp, ?_⟩
    exact (actualHubbard_effectiveForm m U V hsymm hdiag left right t J
      hloop hsimple hgap hcal p).symm

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardFermionSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete half-filled Fock variational problem has the concrete block form. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem euclidean_real_inner {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  rfl

theorem coordinateInclusion_real_inner {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) :
    ⟪coordinateInclusion f x, y⟫_ℝ = ⟪x, coordinateRestriction f y⟫_ℝ := by
  rw [euclidean_real_inner, euclidean_real_inner]
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right (coordinateInclusion f) x y).symm

theorem coordinateRestriction_inclusion {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (x : EuclideanSpace ℂ α) :
    coordinateRestriction f (coordinateInclusion f x) = x := by
  ext a
  rw [coordinateRestriction_apply, coordinateInclusion_apply_image f hf]

theorem lowFock_real_inner (m : ℕ) (p : ActualHubbardLowSpace m)
    (v : FockCoordinateSpace (2 * m + 1)) :
    ⟪lowFockInclusion m p, v⟫_ℝ = ⟪p, lowFockRestriction m v⟫_ℝ :=
  coordinateInclusion_real_inner _ p v

theorem highFock_real_inner (m : ℕ) (q : ActualHubbardHighSpace m)
    (v : FockCoordinateSpace (2 * m + 1)) :
    ⟪highFockInclusion m q, v⟫_ℝ = ⟪q, highFockRestriction m v⟫_ℝ :=
  coordinateInclusion_real_inner _ q v

theorem highFockRestriction_inclusion (m : ℕ) (q : ActualHubbardHighSpace m) :
    highFockRestriction m (highFockInclusion m q) = q :=
  coordinateRestriction_inclusion _ (highOccupationIndex_injective m) q

theorem lowFockInclusion_norm_map (m : ℕ) (p : ActualHubbardLowSpace m) :
    ‖lowFockInclusion m p‖ = ‖p‖ :=
  coordinateInclusion_norm_map _ (spinOccupationSet_injective m) p

theorem highFockInclusion_norm_map (m : ℕ) (q : ActualHubbardHighSpace m) :
    ‖highFockInclusion m q‖ = ‖q‖ :=
  coordinateInclusion_norm_map _ (highOccupationIndex_injective m) q

theorem highOccupationIndex_ne_spin (m : ℕ) (A : HalfFilledHighBasis m)
    (s : SourceSpinBasis (m + 1)) : highOccupationIndex m A ≠ spinOccupationSet m s := by
  intro h
  apply A.property
  intro i
  change occupationAt m (highOccupationIndex m A) i = 1
  rw [h, occupationAt_spinOccupationSet]

theorem lowFockRestriction_highInclusion (m : ℕ) (q : ActualHubbardHighSpace m) :
    lowFockRestriction m (highFockInclusion m q) = 0 := by
  ext s
  change coordinateRestriction (spinOccupationSet m) (highFockInclusion m q) s = 0
  rw [coordinateRestriction_apply]
  exact coordinateInclusion_apply_outside _ q _ (fun A => highOccupationIndex_ne_spin m A s)

theorem low_high_inner_zero (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    ⟪lowFockInclusion m p, highFockInclusion m q⟫_ℝ = 0 := by
  rw [lowFock_real_inner, lowFockRestriction_highInclusion, inner_zero_right]

theorem low_high_norm_sq (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    ‖lowFockInclusion m p + highFockInclusion m q‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  rw [norm_add_sq_real, low_high_inner_zero, mul_zero, add_zero,
    lowFockInclusion_norm_map, highFockInclusion_norm_map]

theorem lowProjection_add_highProjection (m : ℕ) (x : Laughlin.Fock.Space (2 * m + 1))
    (hx : IsHalfFilled m x) : lowProjection m x + highProjection m x = x := by
  apply (fockBasis (2 * m + 1)).repr.injective
  ext A
  simp only [map_add, Finsupp.add_apply, lowProjection, occupationDiagonal,
    highProjection, fockDiagonal_coordinate]
  by_cases hspin : ∀ i, occupationAt m A i = 1
  · simp [hspin]
  · by_cases hcard : A.card = m + 1
    · simp [hspin, hcard]
    · simp [hspin, hcard, hx A hcard]

theorem assembleFock_mass (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    fockMass (assembleFock m p q) = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  rw [← fockCoordinates_norm_sq, fockCoordinates_assemble, low_high_norm_sq]

theorem assembleFock_halfFilled (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    IsHalfFilled m (assembleFock m p q) := by
  intro A hA
  have hl : ∀ s, spinOccupationSet m s ≠ A := by
    intro s hs
    exact hA (hs ▸ spinOccupationSet_card m s)
  have hh : ∀ B, highOccupationIndex m B ≠ A := by
    intro B hB
    exact hA (hB ▸ B.val.property)
  change fockCoordinates (2 * m + 1) (assembleFock m p q) A = 0
  rw [fockCoordinates_assemble]
  simp only [PiLp.add_apply]
  change coordinateInclusion (spinOccupationSet m) p A +
    coordinateInclusion (highOccupationIndex m) q A = 0
  rw [coordinateInclusion_apply_outside _ p A hl,
    coordinateInclusion_apply_outside _ q A hh, add_zero]

/-- Every vector in the full half-filled Fock sector has this low/high
decomposition, not just vectors generated by a trial-state ansatz. -/
theorem assembleFock_decomposition (m : ℕ) (x : Laughlin.Fock.Space (2 * m + 1))
    (hx : IsHalfFilled m x) :
    assembleFock m (lowFockRestriction m (fockCoordinates (2 * m + 1) x))
      (highFockRestriction m (fockCoordinates (2 * m + 1) x)) = x := by
  apply (fockCoordinates (2 * m + 1)).injective
  rw [fockCoordinates_assemble, lowFock_projector_coordinates, highFock_projector_coordinates,
    ← map_add, lowProjection_add_highProjection m x hx]

theorem chargePenaltyFock_spinEmbedding (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ) (u : SourceSpinVector (m + 1)) :
    chargePenaltyFock m U V (spinEmbedding m u) = 0 := by
  have hsingle (s : SourceSpinBasis (m + 1)) : chargePenaltyFock m U V (spinWedge m s) = 0 := by
    have h := occupationDiagonal_eigen m (fun o => (chargePenalty U V o : ℂ))
      (fun _ => 1) (spinWedge m s) (fun k => by simpa using siteNumber_spinWedge m s k)
    simpa [chargePenaltyFock, chargePenalty, occupationDeviation] using h
  change chargePenaltyFock m U V (∑ s, u s • spinWedge m s) = _
  simp only [map_sum, map_smul, hsingle, smul_zero, Finset.sum_const_zero]

theorem chargePenaltyFock_highInclusion (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ) (q : ActualHubbardHighSpace m) :
    fockOperator (chargePenaltyFock m U V) (highFockInclusion m q) =
      highFockInclusion m (actualChargePenalty m U V q) := by
  ext A
  rw [chargePenaltyFock, occupationDiagonal, fockOperator_diagonal_apply]
  change _ * coordinateInclusion (highOccupationIndex m) q A =
    coordinateInclusion (highOccupationIndex m) (actualChargePenalty m U V q) A
  by_cases hA : ∃ B, highOccupationIndex m B = A
  · obtain ⟨B, rfl⟩ := hA
    rw [coordinateInclusion_apply_image _ (highOccupationIndex_injective m),
      coordinateInclusion_apply_image _ (highOccupationIndex_injective m)]
    rfl
  · rw [coordinateInclusion_apply_outside _ _ A (by simpa using hA),
      coordinateInclusion_apply_outside _ _ A (by simpa using hA), mul_zero]

variable {Edge : Type*} [Fintype Edge]

theorem lowFockRestriction_hopping_low (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e) (p : ActualHubbardLowSpace m) :
    lowFockRestriction m
      (fockOperator (graphHopping m left right (fun e => (t e : ℂ))) (lowFockInclusion m p)) = 0 := by
  have hinput : fockOperator (graphHopping m left right (fun e => (t e : ℂ)))
      (lowFockInclusion m p) = fockCoordinates (2 * m + 1)
        (graphHopping m left right (fun e => (t e : ℂ)) (spinEmbedding m (fun s => p s))) := by
    rw [lowFockInclusion_spinEmbedding, fockOperator_coordinates]
  apply lowFockInclusion_injective m
  rw [hinput, lowFock_projector_coordinates,
    lowProjection_graphHopping_spinEmbedding_zero m left right _ hloop, map_zero, map_zero]

theorem fockHopping_real_symmetric (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (v w : FockCoordinateSpace (2 * m + 1)) :
    ⟪v, fockOperator (graphHopping m left right (fun e => (t e : ℂ))) w⟫_ℝ =
      ⟪fockOperator (graphHopping m left right (fun e => (t e : ℂ))) v, w⟫_ℝ := by
  rw [euclidean_real_inner, euclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right
    (fockOperator (graphHopping m left right (fun e => (t e : ℂ)))) v w
  rw [fockOperator_graphHopping_adjoint] at h
  exact congrArg Complex.re h

theorem hubbardFermionForm_blocks (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    hubbardFermionForm m U V left right t (assembleFock m p q) =
      Perturbation.blockEnergy (actualChargePenalty m U V)
        (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t) p q := by
  let H := fockOperator (graphHopping m left right (fun e => (t e : ℂ)))
  let P := fockOperator (chargePenaltyFock m U V)
  let lp := lowFockInclusion m p
  let hq := highFockInclusion m q
  have hPlow : P lp = 0 := by
    dsimp only [P, lp]
    rw [lowFockInclusion_spinEmbedding, fockOperator_coordinates,
      chargePenaltyFock_spinEmbedding, map_zero]
  have hPhigh : P hq = highFockInclusion m (actualChargePenalty m U V q) :=
    chargePenaltyFock_highInclusion m U V q
  have hPenaltyCross : ⟪lp, P hq⟫_ℝ = 0 := by
    rw [hPhigh, low_high_inner_zero]
  have hPenaltyHigh : ⟪hq, P hq⟫_ℝ = ⟪q, actualChargePenalty m U V q⟫_ℝ := by
    rw [hPhigh, highFock_real_inner, highFockRestriction_inclusion]
  have hHopLow : ⟪lp, H lp⟫_ℝ = 0 := by
    rw [lowFock_real_inner, lowFockRestriction_hopping_low m left right t hloop,
      inner_zero_right]
  have hHopCross : ⟪hq, H lp⟫_ℝ = ⟪q, actualHubbardCoupling m left right t p⟫_ℝ := by
    rw [highFock_real_inner]
    rfl
  have hHopReverse : ⟪lp, H hq⟫_ℝ = ⟪q, actualHubbardCoupling m left right t p⟫_ℝ := by
    rw [fockHopping_real_symmetric, real_inner_comm, hHopCross]
  have hHopHigh : ⟪hq, H hq⟫_ℝ = ⟪q, actualHubbardHighHopping m left right t q⟫_ℝ := by
    rw [highFock_real_inner]
    rfl
  have hform : hubbardFermionForm m U V left right t (assembleFock m p q) =
      ⟪lp + hq, P (lp + hq) + H (lp + hq)⟫_ℝ := by
    unfold hubbardFermionForm
    rw [LinearMap.add_apply, map_add, ← fockOperator_coordinates, ← fockOperator_coordinates,
      fockCoordinates_assemble]
  rw [hform, map_add, map_add]
  simp only [inner_add_left, inner_add_right, hPlow, inner_zero_right,
    hPenaltyCross, hPenaltyHigh, hHopLow, hHopCross, hHopReverse, hHopHigh]
  unfold Perturbation.blockEnergy Perturbation.penaltyForm
  ring

theorem hubbardFermionBottom_eq_blockBottom (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e) :
    hubbardFermionBottom m U V left right t =
      Perturbation.blockBottom (actualChargePenalty m U V)
        (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t) := by
  unfold hubbardFermionBottom Perturbation.blockBottom
  congr 1
  ext e
  constructor
  · rintro ⟨x, hx, hmass, rfl⟩
    let p := lowFockRestriction m (fockCoordinates (2 * m + 1) x)
    let q := highFockRestriction m (fockCoordinates (2 * m + 1) x)
    have hdecomp : assembleFock m p q = x := assembleFock_decomposition m x hx
    have hnorm : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
      rw [← assembleFock_mass, hdecomp]
      exact hmass
    refine ⟨p, q, hnorm, ?_⟩
    rw [← hdecomp, hubbardFermionForm_blocks m U V left right t hloop, assembleFock_mass]
    rfl
  · rintro ⟨p, q, hnorm, rfl⟩
    refine ⟨assembleFock m p q, assembleFock_halfFilled m p q, ?_, ?_⟩
    · rw [assembleFock_mass]
      exact hnorm
    · rw [hubbardFermionForm_blocks m U V left right t hloop, assembleFock_mass]
      rfl

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GramPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit-charge application uses full Coulomb Gram coercivity rather
than absolute row dominance. These supporting estimates keep the actual
long-range penalty and its exact hole-double denominator. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

/-- Full quadratic coercivity gives a gap on every half-filled charge defect. -/
theorem chargePenalty_Gram_gap {m : ℕ} (U c : ℝ) (V : Fin m → Fin m → ℝ)
    (hc : 0 ≤ c)
    (hGram : ∀ d : Fin m → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (occupation : Fin m → Fin 3) (hfill : ∑ i, (occupation i : ℕ) = m)
    (hdefect : ¬∀ i, occupation i = 1) : c ≤ chargePenalty U V occupation := by
  have hquad := hGram (occupationDeviation occupation)
  have hsize := occupation_defect_size occupation hfill hdefect
  have hproduct := mul_nonneg hc (sub_nonneg.mpr hsize)
  unfold chargePenalty
  nlinarith

/-- The same Gram condition controls the physical virtual excitation
without replacing its exact denominator by the global coercivity constant. -/
theorem chargeTransfer_Gram_denominator {m : ℕ} (U c : ℝ) (V : Fin m → Fin m → ℝ)
    (hGram : ∀ d : Fin m → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (hole double : Fin m) (hne : hole ≠ double)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0) :
    c ≤ U - V hole double := by
  have hquad := hGram (occupationDeviation (chargeTransferOccupation hole double))
  have hpen := chargeTransfer_penalty U V hole double hne hsymm hdiag
  unfold chargePenalty at hpen
  rw [chargeTransfer_deviation_sq_sum hole double hne] at hquad hpen
  nlinarith

theorem chargePenalty_Gram_inverse_data {m : ℕ} {Basis : Type*} [Fintype Basis]
    (U c : ℝ) (V : Fin m → Fin m → ℝ) (occupation : Basis → Fin m → Fin 3)
    (hc : 0 < c)
    (hGram : ∀ d : Fin m → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (hfill : ∀ s, ∑ i, (occupation s i : ℕ) = m) :
    let weight : ChargeHighBasis occupation → ℝ :=
      fun s => chargePenalty U V (occupation s.val)
    (∀ x, diagonalPenalty weight (diagonalPenalty (fun s => (weight s)⁻¹) x) = x) ∧
      ‖diagonalPenalty (fun s => (weight s)⁻¹)‖ ≤ 1 / c ∧
      (∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty weight x⟫_ℝ) := by
  classical
  intro weight
  have hgap (s : ChargeHighBasis occupation) : c ≤ weight s :=
    chargePenalty_Gram_gap U c V hc.le hGram (occupation s.val) (hfill s.val) s.property
  exact ⟨diagonalPenalty_inverse_right weight (fun s => ne_of_gt (hc.trans_le (hgap s))),
    diagonalPenalty_inverse_norm hc weight hgap, diagonalPenalty_gap weight c hgap⟩

namespace HubbardGlobal
variable {Edge : Type*} [Fintype Edge]

/-- Actual full Fock blocks, with smallness measured against the Gram gap. -/
theorem actual_hubbard_Gram_second_order (m : ℕ) (U c : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ) (hc : 0 < c)
    (hGram : ∀ d : Fin (m + 1) → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |t e| ≤ epsilon * c) :
    let weight : HalfFilledHighBasis m → ℝ :=
      fun A => chargePenalty U V (occupationAt m A.val.val)
    |Perturbation.blockBottom (diagonalPenalty weight)
        (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t) -
      Perturbation.effectiveBottom (0 : ActualHubbardLowSpace m →L[ℝ] ActualHubbardLowSpace m)
        (diagonalPenalty (fun A => (weight A)⁻¹)) (actualHubbardCoupling m left right t)| ≤
      2 * c * epsilon ^ 3 := by
  classical
  intro weight
  obtain ⟨hAT, hT, hgap⟩ := chargePenalty_Gram_inverse_data U c V
    (fun A : HalfFilledBasis m => occupationAt m A.val) hc hGram (halfFilled_occupation_sum m)
  exact Perturbation.finite_blockBottom_second_order
    (diagonalPenalty weight) (diagonalPenalty (fun A => (weight A)⁻¹))
    (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t)
    hc hepsilon hsmall hAT (diagonalPenalty_symmetric weight)
    (fun x => (mul_nonneg hc.le (sq_nonneg ‖x‖)).trans (hgap x))
    hgap hT ((actualHubbardCoupling_norm m left right t).trans ht)
    ((actualHubbardHighHopping_norm m left right t).trans ht)
    (hubbardLowUnit (m + 1)) (hubbardLowUnit_norm (m + 1))

/-- Complete fixed-particle fermion-to-spin spectrum under full Gram
coercivity. The exact denominators U−Vij follow from that same condition. -/
theorem hubbardFermionBottom_Gram_Heisenberg (m : ℕ) (U c : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0) (hc : 0 < c)
    (hGram : ∀ d : Fin (m + 1) → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hcal : ∀ e, t e ^ 2 = J e * (U - V (left e) (right e)))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |t e| ≤ epsilon * c) :
    |hubbardFermionBottom m U V left right t - graphSourceBottom m left right J| ≤
      2 * c * epsilon ^ 3 := by
  have hgap (e : Edge) : U - V (left e) (right e) ≠ 0 :=
    ne_of_gt (hc.trans_le (chargeTransfer_Gram_denominator U c V hGram
      (left e) (right e) (hloop e) hsymm hdiag))
  rw [hubbardFermionBottom_eq_blockBottom m U V left right t hloop,
    ← actualHubbard_effectiveBottom m U V hsymm hdiag left right t J
      hloop hsimple hgap hcal]
  exact actual_hubbard_Gram_second_order m U c V hc hGram left right t hepsilon hsmall ht

end HubbardGlobal
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singlet and excited mediator coordinates form the full spin space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

@[simp] theorem mediatorLowRestriction_apply (n r : ℕ) (x : MediatorFullSpace n r)
    (s : SourceSpinBasis n) : mediatorLowRestriction n r x s = x (s, mediatorVacuum r) :=
  HubbardGlobal.coordinateRestriction_apply _ x s

@[simp] theorem mediatorHighRestriction_apply (n r : ℕ) (x : MediatorFullSpace n r)
    (s : SourceSpinBasis n × MediatorHighBasis r) :
    mediatorHighRestriction n r x s = x (s.1, s.2.val) :=
  HubbardGlobal.coordinateRestriction_apply _ x s

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_BinaryEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit prefix-free binary encodings for finite source and circuit data.
Natural numbers use their binary digits, with one marker bit per digit.
Pairs concatenate; lists have a binary length header. In particular, list
serialization does not repeatedly pair large natural-number codes. -/

namespace ContinuumCoulomb
namespace BinaryEncoding

theorem list_length {α : Type*} (a : Codec α) (xs : List α) :
    ((list a).encode xs).length = 2 * xs.length.size + 1 +
      (xs.map (fun x => (a.encode x).length)).sum := by
  simp only [list, List.length_append, natural_length, List.length_flatMap]

end BinaryEncoding
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BinaryRoots
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

/-- The returned integer brackets the true square root by adjacent integers. -/
theorem root_spec (m : ℕ) : root m ^ 2 ≤ m ∧ m < (root m + 1) ^ 2 := by
  apply ExactQuantumFactoring.Primality.boundedRoot_spec (by decide)
  simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self m

end ContinuumCoulomb.SquareRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_DyadicRootProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b N F : ℕ) (hF : 0 < F) :
    0 ≤ Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) ∧
      Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) < 1 / (2 : ℝ) ^ b := by
  let p : ℕ := 2 ^ b
  let m : ℕ := N * p ^ 2 / F
  let r : ℕ := SquareRootProgram.root m
  have hp : (0 : ℝ) < p := by dsimp [p]; positivity
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hlo : r ^ 2 * F ≤ N * p ^ 2 :=
    (Nat.mul_le_mul_right F (SquareRootProgram.root_spec m).1).trans (Nat.div_mul_le_self _ _)
  have hhi : N * p ^ 2 < (r + 1) ^ 2 * F :=
    (Nat.div_lt_iff_lt_mul hF).mp (SquareRootProgram.root_spec m).2
  have hlo' : (r : ℝ) ^ 2 * F ≤ (N : ℝ) * (p : ℝ) ^ 2 := by exact_mod_cast hlo
  have hhi' : (N : ℝ) * (p : ℝ) ^ 2 < ((r : ℝ) + 1) ^ 2 * F := by exact_mod_cast hhi
  have hrad : 0 ≤ (N : ℝ) / F := by positivity
  have hsquare : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 * F = (N : ℝ) * (p : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp [hFr.ne']
  have hs : 0 ≤ Real.sqrt ((N : ℝ) / F) * p := by positivity
  have hslo : (r : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / F) * p) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hlo'
  have hshi : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 < ((r : ℝ) + 1) ^ 2 := by
    apply (mul_lt_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hhi'
  have hl : (r : ℝ) ≤ Real.sqrt ((N : ℝ) / F) * p := by
    nlinarith only [hslo, hs, show 0 ≤ (r : ℝ) by positivity]
  have hu : Real.sqrt ((N : ℝ) / F) * p < (r : ℝ) + 1 := by
    nlinarith only [hshi, hs, show 0 ≤ (r : ℝ) by positivity]
  have hvalue : (value b N F : ℝ) = (r : ℝ) / p := by
    simp only [value, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, p, r, m,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpcast : (p : ℝ) = (2 : ℝ) ^ b := by simp only [p, Nat.cast_pow, Nat.cast_ofNat]
  rw [hvalue, ← hpcast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr hl)
  · apply (lt_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    linarith

end ContinuumCoulomb.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorParameters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial scales and rational positive spokes for one actual
simultaneous singlet-mediator stage. The norm hypothesis concerns the
unchanged low-block terms; no spectral conclusion is assumed. -/

namespace ContinuumCoulomb.MediatorParameters
open scoped BigOperators Kronecker InnerProductSpace

theorem scale_pos (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G) : 0 < scale r W G := by
  unfold scale
  positivity

theorem scale_lower (r : ℕ) {W G : ℕ} (_hW : 0 < W) (hG : 0 < G) :
    16 * (r + 1) * W ≤ scale r W G := by
  have hrpow := Nat.le_self_pow (by decide : 3 ≠ 0) (r + 1)
  have hWpow := Nat.le_self_pow (by decide : 3 ≠ 0) W
  calc
    _ ≤ 1048576 * (r + 1) * W := by gcongr; norm_num
    _ ≤ 1048576 * (r + 1) ^ 3 * W ^ 3 * G := by
      calc
        _ ≤ 1048576 * (r + 1) ^ 3 * W ^ 3 := by gcongr
        _ ≤ _ := Nat.le_mul_of_pos_right _ hG
    _ = scale r W G := rfl

theorem canonical_amplitude_upper (r : ℕ) {W G : ℕ} (hW : 0 < W) (_hG : 0 < G)
    {J : ℝ} (hJ : |J| ≤ W) :
    signedMediatorAmplitude (delta r W G : ℝ) J ≤ 2 * (scale r W G : ℝ) * W := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW2 : (W : ℝ) ≤ 2 * (W : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left (hJ.trans hW2)
    (show 0 ≤ 2 * (scale r W G : ℝ) ^ 2 by positivity)
  unfold signedMediatorAmplitude
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  unfold delta
  push_cast
  nlinarith only [hmul]

theorem canonical_amplitude_lower (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℝ} (hJ : 1 / (W : ℝ) ≤ |J|) :
    1 ≤ signedMediatorAmplitude (delta r W G : ℝ) J := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hSl : (W : ℝ) ≤ scale r W G := by
    have h := scale_lower r hW hG
    have : W ≤ scale r W G := by nlinarith
    exact_mod_cast this
  have hS1 : (1 : ℝ) ≤ scale r W G := by exact_mod_cast scale_pos r hW hG
  have hmul : 1 ≤ (W : ℝ) * |J| := by
    simpa only [mul_comm] using (div_le_iff₀ hWr).mp hJ
  have hSW : (W : ℝ) ≤ (scale r W G : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hSW (abs_nonneg J)
  unfold signedMediatorAmplitude
  apply Real.le_sqrt_of_sq_le
  unfold delta
  push_cast
  nlinarith

theorem rational_sqrt_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    0 ≤ Real.sqrt (q : ℝ) - (DyadicRootProgram.value b q.num.toNat q.den : ℝ) ∧
      Real.sqrt (q : ℝ) - (DyadicRootProgram.value b q.num.toNat q.den : ℝ) < 1 / (2 : ℝ) ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  simpa only [hre] using DyadicRootProgram.value_error b q.num.toNat q.den q.pos

theorem spoke_error (r W G : ℕ) (J : ℚ) :
    0 ≤ signedMediatorAmplitude (delta r W G : ℝ) (J : ℝ) - (spoke r W G J : ℝ) ∧
      signedMediatorAmplitude (delta r W G : ℝ) (J : ℝ) - (spoke r W G J : ℝ) <
        1 / (2 : ℝ) ^ precision r G := by
  have h := rational_sqrt_error (precision r G)
    (show 0 ≤ radicand r W G J by unfold radicand; positivity)
  simpa only [spoke, radicand, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_abs, signedMediatorAmplitude] using h

end ContinuumCoulomb.MediatorParameters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorScaleBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete weight and inverse-weight bounds for the three mediator
stages. Each bound is a fixed polynomial in entering unary parameters. -/

namespace ContinuumCoulomb.MediatorParameters

theorem spoke_lower_half (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : 1 / (W : ℝ) ≤ |(J : ℝ)|) :
    (1 / 2 : ℝ) ≤ spoke r W G J := by
  have ha := canonical_amplitude_lower r hW hG hJ
  have he := (spoke_error r W G J).2
  have hpower : (2 : ℝ) ≤ (2 : ℝ) ^ precision r G := by
    exact_mod_cast Nat.le_self_pow (by unfold precision; omega : precision r G ≠ 0) 2
  have hp : 1 / (2 : ℝ) ^ precision r G ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hpower
  linarith

theorem spoke_upper (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ W) :
    (spoke r W G J : ℝ) ≤ 2 * (scale r W G : ℝ) * W := by
  have he := (spoke_error r W G J).1
  have ha := canonical_amplitude_upper r hW hG hJ
  linarith

theorem secondWeight_two_le (r W G : ℕ) : 2 ≤ secondWeight r W G := by
  unfold secondWeight
  omega

theorem thirdWeight_two_le (r W G : ℕ) : 2 ≤ thirdWeight r W G := by
  unfold thirdWeight
  omega

theorem second_spoke_bounds (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ W) (hJlower : 1 / (W : ℝ) ≤ |(J : ℝ)|) :
    1 / (secondWeight r W G : ℝ) ≤ |(spoke r W G J : ℝ)| ∧
      |(spoke r W G J : ℝ)| ≤ secondWeight r W G := by
  have hl := spoke_lower_half r hW hG hJlower
  have hu := spoke_upper r hW hG hJ
  have htwo : (2 : ℝ) ≤ secondWeight r W G := by exact_mod_cast secondWeight_two_le r W G
  have hmax : 2 * (scale r W G : ℝ) * W ≤ secondWeight r W G := by
    exact_mod_cast (show 2 * scale r W G * W ≤ secondWeight r W G by unfold secondWeight; omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ spoke r W G J)]
  exact ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans hl, hu.trans hmax⟩

theorem third_spoke_bounds (r : ℕ) {W G : ℕ} (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ secondWeight r W G)
    (hJlower : 1 / (secondWeight r W G : ℝ) ≤ |(J : ℝ)|) :
    1 / (thirdWeight r W G : ℝ) ≤
        |(spoke (2 * r) (secondWeight r W G) G J : ℝ)| ∧
      |(spoke (2 * r) (secondWeight r W G) G J : ℝ)| ≤ thirdWeight r W G := by
  have hW2 : 0 < secondWeight r W G := lt_of_lt_of_le (by norm_num) (secondWeight_two_le r W G)
  have hl := spoke_lower_half (2 * r) hW2 hG hJlower
  have hu := spoke_upper (2 * r) hW2 hG hJ
  have htwo : (2 : ℝ) ≤ thirdWeight r W G := by exact_mod_cast thirdWeight_two_le r W G
  have hmax : 2 * (scale (2 * r) (secondWeight r W G) G : ℝ) * secondWeight r W G ≤
      thirdWeight r W G := by
    exact_mod_cast (show 2 * scale (2 * r) (secondWeight r W G) G * secondWeight r W G ≤
      thirdWeight r W G by unfold thirdWeight; omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ spoke (2 * r) (secondWeight r W G) G J)]
  exact ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans hl, hu.trans hmax⟩

theorem third_central_bounds (r : ℕ) {W G : ℕ} (hG : 0 < G) :
    1 / (thirdWeight r W G : ℝ) ≤ delta (2 * r) (secondWeight r W G) G ∧
      (delta (2 * r) (secondWeight r W G) G : ℝ) ≤ thirdWeight r W G := by
  have hW2 : 0 < secondWeight r W G := lt_of_lt_of_le (by norm_num) (secondWeight_two_le r W G)
  have hdelta : (1 : ℝ) ≤ delta (2 * r) (secondWeight r W G) G := by
    have hp : 0 < delta (2 * r) (secondWeight r W G) G := by
      unfold delta
      exact pow_pos (scale_pos (2 * r) hW2 hG) 2
    exact_mod_cast hp
  have htwo : (2 : ℝ) ≤ thirdWeight r W G := by exact_mod_cast thirdWeight_two_le r W G
  refine ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans (by linarith), ?_⟩
  exact_mod_cast (show delta (2 * r) (secondWeight r W G) G ≤ thirdWeight r W G by
    unfold thirdWeight; omega)

end ContinuumCoulomb.MediatorParameters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorIteration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual mediator stages. Only the original central bonds
survive the last subdivision; each original spoke becomes a nine-link
path, giving eighteen new spins and nineteen positive bonds per edge. -/

namespace ContinuumCoulomb.MediatorIteration
open Matrix MediatorGraph
open scoped BigOperators Kronecker InnerProductSpace

theorem lift_noLoops {n q : ℕ} (r : ℕ) (F : Bonds n q) (hF : F.NoLoops) :
    (lift r F).NoLoops := by
  intro e h
  exact hF e (old_injective n r h)

theorem central_noLoops (n r : ℕ) (Delta : ℚ) : (central n r Delta).NoLoops := by
  intro e h
  have hpair := fresh_injective n r (a₁ := (e, 0)) (a₂ := (e, 1)) h
  have := congrArg Prod.snd hpair
  norm_num at this

theorem spokes_noLoops {n r : ℕ} (F : Bonds n r) (member : Fin r → Fin 2)
    (amplitude : Fin r → ℚ) : (spokes F member amplitude).NoLoops := by
  intro a
  exact old_ne_fresh n r _ _ _

theorem join_noLoops {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (hF : F.NoLoops) (hK : K.NoLoops) : (join F K).NoLoops := by
  intro a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective a
  cases b with
  | inl e => simpa [join] using hF e
  | inr e => simpa [join] using hK e

theorem finalGraph_noLoops {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (finalGraph F W G).NoLoops := by
  exact join_noLoops _ _
    (lift_noLoops _ _ (lift_noLoops _ _ (central_noLoops _ _ _)))
    (join_noLoops _ _ (central_noLoops _ _ _) (spokes_noLoops _ _ _))

theorem join_weight_property {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (P : ℚ → Prop) (hF : ∀ e, P (F.weight e)) (hK : ∀ e, P (K.weight e)) :
    ∀ e, P ((join F K).weight e) := by
  intro e
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective e
  cases a with
  | inl a => simpa [join] using hF a
  | inr a => simpa [join] using hK a

theorem firstSpokes_bounds {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / (secondBound r W G : ℝ) ≤ |((firstSpokes F W G).weight e : ℝ)| ∧
      |((firstSpokes F W G).weight e : ℝ)| ≤ secondBound r W G := by
  intro e
  exact MediatorParameters.second_spoke_bounds r hW hG (hJ _) (hJl _)

theorem secondPaths_bounds {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / (thirdBound r W G : ℝ) ≤ |((secondPaths F W G).weight e : ℝ)| ∧
      |((secondPaths F W G).weight e : ℝ)| ≤ thirdBound r W G := by
  apply join_weight_property _ _
    (fun J => 1 / (thirdBound r W G : ℝ) ≤ |(J : ℝ)| ∧ |(J : ℝ)| ≤ thirdBound r W G)
  · intro e
    have h := MediatorParameters.third_central_bounds r (W := W) hG
    change 1 / (thirdBound r W G : ℝ) ≤ |(deltaTwo r W G : ℝ)| ∧
      |(deltaTwo r W G : ℝ)| ≤ thirdBound r W G
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ deltaTwo r W G)]
    simpa only [deltaTwo, secondBound, thirdBound, Nat.mul_comm] using h
  · intro e
    have hbound := firstSpokes_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1
    have h := MediatorParameters.third_spoke_bounds r hG hbound.2 hbound.1
    simpa only [secondSpokes, spokes, secondBound, thirdBound, Nat.mul_comm] using h

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorPromise
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit final weight bounds and promise thresholds for the actual
three-stage positive-spin graph. -/

namespace ContinuumCoulomb.MediatorIteration
open scoped BigOperators InnerProductSpace

theorem finalGraph_lower {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, (1 / 2 : ℝ) ≤ (finalGraph F W G).weight e := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hdelta1 : (1 : ℝ) ≤ deltaOne r W G := by
    have hp : 0 < deltaOne r W G := by
      unfold deltaOne MediatorParameters.delta
      exact pow_pos (MediatorParameters.scale_pos r hW hG) 2
    exact_mod_cast hp
  have hdelta3 : (1 : ℝ) ≤ deltaThree r W G := by
    have hp : 0 < deltaThree r W G := by
      unfold deltaThree MediatorParameters.delta
      exact pow_pos (MediatorParameters.scale_pos _ hW3 hG) 2
    exact_mod_cast hp
  apply join_weight_property _ _ (fun J => (1 / 2 : ℝ) ≤ J)
  · intro e
    change (1 / 2 : ℝ) ≤ ((deltaOne r W G : ℚ) : ℝ)
    simpa only [Rat.cast_natCast] using (show (1 / 2 : ℝ) ≤ deltaOne r W G by linarith)
  · apply join_weight_property _ _ (fun J => (1 / 2 : ℝ) ≤ J)
    · intro e
      change (1 / 2 : ℝ) ≤ ((deltaThree r W G : ℚ) : ℝ)
      simpa only [Rat.cast_natCast] using (show (1 / 2 : ℝ) ≤ deltaThree r W G by linarith)
    · intro e
      exact MediatorParameters.spoke_lower_half _ hW3 hG
        (secondPaths_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1).1

theorem finalGraph_upper {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, ((finalGraph F W G).weight e : ℝ) ≤ MediatorParameters.finalWeight r W G := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hr : r * 2 + r * 2 * 2 = 6 * r := by omega
  have hdelta1 : deltaOne r W G ≤ MediatorParameters.finalWeight r W G := by
    unfold deltaOne MediatorParameters.finalWeight
    omega
  have hdelta3 : deltaThree r W G ≤ MediatorParameters.finalWeight r W G := by
    unfold deltaThree thirdBound
    rw [hr]
    unfold MediatorParameters.finalWeight
    omega
  have hspoke : 2 * MediatorParameters.scale (r * 2 + r * 2 * 2) (thirdBound r W G) G * thirdBound r W G ≤
      MediatorParameters.finalWeight r W G := by
    unfold thirdBound
    rw [hr]
    unfold MediatorParameters.finalWeight
    omega
  apply join_weight_property _ _ (fun J => (J : ℝ) ≤ MediatorParameters.finalWeight r W G)
  · intro e
    change ((deltaOne r W G : ℚ) : ℝ) ≤ _
    exact_mod_cast hdelta1
  · apply join_weight_property _ _ (fun J => (J : ℝ) ≤ MediatorParameters.finalWeight r W G)
    · intro e
      change ((deltaThree r W G : ℚ) : ℝ) ≤ _
      exact_mod_cast hdelta3
    · intro e
      have h := MediatorParameters.spoke_upper (r * 2 + r * 2 * 2) hW3 hG
        (secondPaths_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1).2
      apply h.trans
      exact_mod_cast hspoke

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSimple
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fresh mediator pairs give a simple unordered edge enumeration. This
supplies the cross-edge cancellation hypothesis in the global Hubbard model. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorGraph

theorem edgeMatches_symm {α : Type*} {a b c d : α}
    (h : edgeMatches a b c d) : edgeMatches c d a b := by
  rcases h with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.2.symm, h.1.symm⟩

theorem Bonds.Simple.hypothesis {n r : ℕ} {F : Bonds n r} (hF : F.Simple) :
    ∀ e f, e ≠ f →
      ¬(F.left e = F.left f ∧ F.right e = F.right f) ∧
      ¬(F.left e = F.right f ∧ F.right e = F.left f) := by
  intro e f hne
  exact ⟨fun h => hne (hF e f (Or.inl h)), fun h => hne (hF e f (Or.inr h))⟩

theorem lift_simple {n q : ℕ} (r : ℕ) (F : Bonds n q) (hF : F.Simple) :
    (lift r F).Simple := by
  intro e f h
  apply hF e f
  rcases h with h | h
  · exact Or.inl ⟨old_injective n r h.1, old_injective n r h.2⟩
  · exact Or.inr ⟨old_injective n r h.1, old_injective n r h.2⟩

theorem central_simple (n r : ℕ) (Delta : ℚ) : (central n r Delta).Simple := by
  intro e f h
  change edgeMatches (fresh n r e 0) (fresh n r e 1)
    (fresh n r f 0) (fresh n r f 1) at h
  rcases h with h | h
  · exact congrArg Prod.fst (fresh_injective n r (a₁ := (e, 0)) (a₂ := (f, 0)) h.1)
  · have hs := congrArg Prod.snd (fresh_injective n r (a₁ := (e, 0)) (a₂ := (f, 1)) h.1)
    norm_num at hs

theorem spokes_simple {n r : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℚ) :
    (spokes F member amplitude).Simple := by
  intro e f h
  obtain ⟨⟨a, s⟩, rfl⟩ := finProdFinEquiv.surjective e
  obtain ⟨⟨b, t⟩, rfl⟩ := finProdFinEquiv.surjective f
  simp only [edgeMatches, spokes, Equiv.symm_apply_apply] at h
  rcases h with h | h
  · have hab := congrArg Prod.fst (fresh_injective n r
      (a₁ := (a, if s = 0 then 0 else member a))
      (a₂ := (b, if t = 0 then 0 else member b)) h.2)
    dsimp only at hab
    subst b
    fin_cases s <;> fin_cases t
    · rfl
    · exact False.elim (hF a (old_injective n r (by simpa using h.1)))
    · exact False.elim (hF a (old_injective n r (by simpa using h.1)).symm)
    · rfl
  · exact False.elim (old_ne_fresh n r _ _ _ h.1)

theorem join_simple {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (hF : F.Simple) (hK : K.Simple)
    (hcross : ∀ e f, ¬edgeMatches (F.left e) (F.right e) (K.left f) (K.right f)) :
    (join F K).Simple := by
  intro e f h
  obtain ⟨e, rfl⟩ := finSumFinEquiv.surjective e
  obtain ⟨f, rfl⟩ := finSumFinEquiv.surjective f
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      simp only [join, Equiv.symm_apply_apply, Sum.elim_inl] at h
      exact congrArg (fun i => finSumFinEquiv (Sum.inl i)) (hF e f h)
    | inr f =>
      simp only [join, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] at h
      exact False.elim (hcross e f h)
  | inr e =>
    cases f with
    | inl f =>
      simp only [join, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] at h
      exact False.elim (hcross f e (edgeMatches_symm h))
    | inr f =>
      simp only [join, Equiv.symm_apply_apply, Sum.elim_inr] at h
      exact congrArg (fun i => finSumFinEquiv (Sum.inr i)) (hK e f h)

theorem central_spokes_simple {n r : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (member : Fin r → Fin 2) (Delta : ℚ) (amplitude : Fin r → ℚ) :
    (join (central n r Delta) (spokes F member amplitude)).Simple := by
  apply join_simple _ _ (central_simple n r Delta) (spokes_simple F hF member amplitude)
  intro e f h
  rcases h with h | h
  · exact old_ne_fresh n r _ _ _ h.1.symm
  · exact old_ne_fresh n r _ _ _ h.2.symm

theorem lift_stage_simple {n q r : ℕ} (K : Bonds n q) (F : Bonds n r)
    (hK : K.Simple) (hF : F.NoLoops) (member : Fin r → Fin 2)
    (Delta : ℚ) (amplitude : Fin r → ℚ) :
    (join (lift r K) (join (central n r Delta) (spokes F member amplitude))).Simple := by
  apply join_simple _ _ (lift_simple r K hK) (central_spokes_simple F hF member Delta amplitude)
  intro e f h
  obtain ⟨f, rfl⟩ := finSumFinEquiv.surjective f
  cases f with
  | inl f =>
    simp only [join, Equiv.symm_apply_apply, Sum.elim_inl] at h
    rcases h with h | h
    · exact old_ne_fresh n r _ _ _ h.1
    · exact old_ne_fresh n r _ _ _ h.1
  | inr f =>
    simp only [join, Equiv.symm_apply_apply, Sum.elim_inr] at h
    rcases h with h | h
    · exact old_ne_fresh n r _ _ _ h.2
    · exact old_ne_fresh n r _ _ _ h.1

theorem finalGraph_simple {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (finalGraph F W G).Simple := by
  apply lift_stage_simple (retainedCentral F W G) (secondPaths F W G)
  · exact lift_simple _ _ (central_simple _ _ _)
  · exact join_noLoops _ _ (central_noLoops _ _ _) (spokes_noLoops _ _ _)

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_Axis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

theorem norm_sq_axis_shift (x : Position) (a : Fin 3) (t : ℝ) :
    ‖x+t • axis a‖^2 = ‖x‖^2 + 2*t*x a + t^2 := by
  rw [norm_add_sq_real]
  simp [axis, inner_smul_right, EuclideanSpace.inner_single_right, norm_smul,
    Real.norm_eq_abs, sq_abs]
  ring

theorem second_deriv_quadratic_rpow {q b p : ℝ} (hq : 0 < q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2 + 2*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      ((hasDerivAt_id t).pow 2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  have hQ0 : Q 0 = q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0 : ℝ), Q t ≠ 0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hder : deriv (fun t => Q t ^ p) =ᶠ[𝓝 0]
      fun t => p*Q t^(p-1)*(2*b+2*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hder.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
      (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul 2))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*2) 0 := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv]
  rw [show p-1-1 = p-2 by ring]
  ring

open scoped Convolution
open ContinuousLinearMap

theorem contDiff_partial {f : Position → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ (n+1) f) (v : Position) : ContDiff ℝ n (dirPartial f v) := by
  exact (hf.fderiv_right le_rfl).clm_apply contDiff_const

theorem hasCompactSupport_partial {f : Position → ℝ} (hf : HasCompactSupport f)
    (v : Position) : HasCompactSupport (dirPartial f v) := hf.fderiv_apply ℝ v

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_WeakLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem integrable_mul_compact_of_continuousAt {f g : Position → ℝ}
    (hf : ∀ x ∈ tsupport g, ContinuousAt f x) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => f x*g x) := by
  have hc : Continuous (fun x => f x*g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport g
    · exact (hf x hx).mul hg.continuousAt
    · have he : (fun y => f y*g y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change g y = 0 at hy
        simp only [hy, mul_zero]
      exact continuousAt_const.congr_of_eventuallyEq he
  exact hc.integrable_of_hasCompactSupport (hgc.mono (Function.support_mul_subset_right f g))

theorem tsupport_dirPartial_subset (f : Position → ℝ) (v : Position) :
    tsupport (dirPartial f v) ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v

theorem integral_mul_coordinateLaplacian_eq {f φ : Position → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, f x * coordinateLaplacian φ x) =
      ∫ x, coordinateLaplacian f x * φ x := by
  have hpφ (v : Position) : ContDiff ℝ ∞ (dirPartial φ v) :=
    contDiff_partial (by simpa using hφ) v
  have hppφ (v : Position) : ContDiff ℝ ∞ (dirPartial (dirPartial φ v) v) :=
    contDiff_partial (by simpa using hpφ v) v
  have hdφ (v : Position) := (hpφ v).differentiable (by simp)
  have hiφ (v : Position) := hasCompactSupport_partial hφc v
  have hpcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ 1 (dirPartial f v) x :=
    ((hf x hx).fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const
  have hppcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContinuousAt (dirPartial (dirPartial f v) v) x :=
    (((hpcont v x hx).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have hleft (v : Position) : Integrable (fun x => f x*dirPartial (dirPartial φ v) v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x ((tsupport_dirPartial_subset φ v)
        (tsupport_dirPartial_subset (dirPartial φ v) v hx))).continuousAt)
      (hppφ v).continuous
      (hasCompactSupport_partial (hiφ v) v)
  have hright (v : Position) : Integrable (fun x => dirPartial (dirPartial f v) v x*φ x) :=
    integrable_mul_compact_of_continuousAt (hppcont v) hφ.continuous hφc
  have hcross (v : Position) : Integrable (fun x => dirPartial f v x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hpcont v x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfg (v : Position) : Integrable (fun x => f x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfpg (v : Position) : Integrable (fun x => dirPartial f v x*φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => (hpcont v x hx).continuousAt)
      hφ.continuous hφc
  have hby (v : Position) :
      (∫ x, f x*dirPartial (dirPartial φ v) v x) = ∫ x, dirPartial (dirPartial f v) v x*φ x := by
    calc
      _ = -(∫ x, dirPartial f v x*dirPartial φ v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).differentiableAt (by norm_num))
          (fun x _ => hdφ v x)
      _ = _ := by
        have he : (∫ x, dirPartial f v x*dirPartial φ v x) =
            -(∫ x, dirPartial (dirPartial f v) v x*φ x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x hx => (hpcont v x hx).differentiableAt (by norm_num))
            (fun x _ => hφ.differentiable (by simp) x)
        rw [he, neg_neg]
  calc
    _ = ∫ x, ∑ a : Fin 3, f x*dirPartial (dirPartial φ (axis a)) (axis a) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coordinateLaplacian_eq_partials (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt, Finset.mul_sum]
    _ = ∑ a : Fin 3, ∫ x, f x*dirPartial (dirPartial φ (axis a)) (axis a) x :=
      integral_finsetSum _ (fun a _ => hleft (axis a))
    _ = ∑ a : Fin 3, ∫ x, dirPartial (dirPartial f (axis a)) (axis a) x*φ x := by
      simp_rw [hby]
    _ = ∫ x, ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x*φ x :=
      (integral_finsetSum _ (fun a _ => hright (axis a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport φ
      · rw [coordinateLaplacian_eq_partials (hf x hx), Finset.sum_mul]
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, Finset.sum_const_zero]

theorem hasCompactSupport_coordinateLaplacian {f : Position → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordinateLaplacian f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_CoulombKernel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem contDiff_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedKernel ε) := by
  apply ContDiff.rpow_const_of_ne
  · exact (contDiff_norm_sq ℝ).add contDiff_const
  · intro x
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)).ne'

theorem laplacian_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) (x : Position) :
    coordinateLaplacian (regularizedKernel ε) x = -regularizedCharge ε x := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have he : ∀ a : Fin 3, (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      (fun t => ((‖x‖^2+ε^2)+2*t*x a+t^2)^(-1/2 : ℝ)) := by
    intro a
    ext t
    unfold regularizedKernel
    rw [norm_sq_axis_shift]
    congr 1
    ring
  unfold coordinateLaplacian
  simp_rw [he, second_deriv_quadratic_rpow hq]
  norm_num
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2+ε^2)^(-5/2 : ℝ)*(‖x‖^2+ε^2) =
      (‖x‖^2+ε^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hq.ne']
    norm_num
  calc
    _ = 3*(‖x‖^2+ε^2)^(-5/2 : ℝ)*(∑ a : Fin 3, (x a)^2) -
        3*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
      rw [Finset.mul_sum]
      congr 1
      all_goals ring_nf
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      unfold regularizedCharge
      rw [← hpow]
      ring

theorem hasDerivAt_chargePrimitive (r : ℝ) :
    HasDerivAt chargePrimitive (3*r^2*(1+r^2)^(-5/2 : ℝ)) r := by
  have hp : 0 < 1+r^2 := by positivity
  have hd := ((hasDerivAt_id r).pow 3).mul
    (((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)).rpow_const
      (p := (-3/2 : ℝ)) (Or.inl hp.ne'))
  unfold chargePrimitive
  apply hd.congr_deriv
  norm_num
  have he : (1+r^2)^(-5/2 : ℝ)*(1+r^2) = (1+r^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hp.ne']; norm_num
  norm_num at he
  rw [← he]
  ring

theorem chargePrimitive_eq_ratio {r : ℝ} (hr : 0 ≤ r) :
    chargePrimitive r = (1-(1+r^2)⁻¹)^(3/2 : ℝ) := by
  have hp : 0 < 1+r^2 := by positivity
  have hh : 1-(1+r^2)⁻¹ = r^2/(1+r^2) := by field_simp; ring
  rw [hh, Real.div_rpow (sq_nonneg _) hp.le]
  have hn : (r^2)^(3/2 : ℝ) = r^3 := by
    rw [← Real.rpow_natCast_mul hr]
    norm_num
  rw [hn]
  unfold chargePrimitive
  rw [show (-3/2:ℝ) = -(3/2:ℝ) by ring, Real.rpow_neg hp.le]
  rfl

theorem tendsto_chargePrimitive : Tendsto chargePrimitive atTop (𝓝 1) := by
  have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hi := tendsto_inv_atTop_zero.comp hp
  have hh := (tendsto_const_nhds.sub hi).rpow tendsto_const_nhds
    (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0) : (1:ℝ)-0 ≠ 0 ∨ 0 < (3/2:ℝ))
  apply Filter.Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  exact (chargePrimitive_eq_ratio hr).symm

theorem integrable_radial_regularizedCharge_one :
    IntegrableOn (fun r : ℝ => 3*r^2*(1+r^2)^(-5/2 : ℝ)) (Set.Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity) tendsto_chargePrimitive

theorem integral_radial_regularizedCharge_one :
    (∫ r : ℝ in Set.Ioi 0, 3*r^2*(1+r^2)^(-5/2 : ℝ)) = 1 := by
  have hder := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0:ℝ)) (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ 3*r^2*(1+r^2)^(-5/2 : ℝ))
    tendsto_chargePrimitive
  simpa [chargePrimitive] using hder

theorem regularizedCharge_one_eq : regularizedCharge 1 =
    fun x : Position => 3*(1+‖x‖^2)^(-5/2 : ℝ) := by
  ext x
  simp [regularizedCharge, add_comm]

theorem integrable_regularizedCharge_one : Integrable (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq, integrable_fun_norm_addHaar volume
    (f := fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simpa [finrank_euclideanSpace_fin, smul_eq_mul, mul_comm, mul_assoc,
    mul_left_comm] using integrable_radial_regularizedCharge_one

theorem integral_regularizedCharge_one : (∫ x, regularizedCharge 1 x) = 4*Real.pi := by
  rw [regularizedCharge_one_eq, integral_fun_norm_addHaar volume
    (fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  norm_num
  have hi : (∫ r : ℝ in Set.Ioi 0, r^2*(3*(1+r^2)^(-(5/2): ℝ))) = 1 := by
    simpa only [neg_div, mul_assoc, mul_comm, mul_left_comm] using
      integral_radial_regularizedCharge_one
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

theorem regularizedCharge_smul {ε : ℝ} (hε : 0 < ε) (x : Position) :
    regularizedCharge ε (ε • x) = (ε^3)⁻¹*regularizedCharge 1 x := by
  unfold regularizedCharge
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have he : (ε*‖x‖)^2+ε^2 = ε^2*(‖x‖^2+1) := by ring
  rw [he, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (ε^2)^(-5/2:ℝ) = (ε^5)⁻¹ := by
    rw [← Real.rpow_natCast_mul hε.le]
    norm_num [Real.rpow_neg hε.le]
  rw [hp]
  norm_num
  field_simp

theorem integral_regularizedCharge_scale {ε : ℝ} (hε : 0 < ε) (φ : Position → ℝ) :
    (∫ x, regularizedCharge ε x*φ x) = ∫ x, regularizedCharge 1 x*φ (ε • x) := by
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (fun x => regularizedCharge ε x*φ x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hs
  have ht : (∫ x, regularizedCharge ε (ε • x)*φ (ε • x)) =
      (ε^3)⁻¹*(∫ x, regularizedCharge 1 x*φ (ε • x)) := by
    simp_rw [regularizedCharge_smul hε, mul_assoc]
    exact integral_const_mul _ _
  rw [ht] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) hs).symm

theorem regularizedCharge_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedCharge ε x := by unfold regularizedCharge; positivity

theorem continuous_regularizedCharge_one : Continuous (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq]
  apply Continuous.const_mul
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    left
    positivity

theorem regularizedCharge_tendsto_dirac {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedCharge (ε n) x*φ x)
      atTop (𝓝 (4*Real.pi*φ 0)) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hD := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Position)) (fun x => regularizedCharge 1 x*C)
    (F := fun n x => regularizedCharge 1 x*φ (ε n • x))
    (f := fun x => regularizedCharge 1 x*φ 0)
    (fun n => (continuous_regularizedCharge_one.mul
      (hφ.comp (show Continuous (fun x : Position => ε n • x) by fun_prop))).aestronglyMeasurable)
    (integrable_regularizedCharge_one.mul_const C)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedCharge_nonneg 1 x)]
      exact mul_le_mul_of_nonneg_left (hC _) (regularizedCharge_nonneg 1 x)))
    (Filter.Eventually.of_forall (fun x => by
      have he : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Position)) := by
        simpa using hlim.smul_const x
      exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp he)))
  simp only [integral_mul_const, integral_regularizedCharge_one] at hD
  simpa only [integral_regularizedCharge_scale (hε _)] using hD

theorem locallyIntegrable_coulombKernel : LocallyIntegrable coulombKernel volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

theorem coulombKernel_eq_rpow (x : Position) :
    coulombKernel x = (‖x‖^2)^(-1/2 : ℝ) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  norm_num [coulombKernel, Real.rpow_neg_one]

theorem regularizedKernel_le {ε : ℝ} {x : Position} (hx : x ≠ 0) :
    regularizedKernel ε x ≤ coulombKernel x := by
  rw [coulombKernel_eq_rpow]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (le_add_of_nonneg_right (sq_nonneg ε)) (by norm_num)

theorem regularizedKernel_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedKernel ε x := by unfold regularizedKernel; positivity

theorem regularizedKernel_tendsto {ε : ℕ → ℝ} (hlim : Tendsto ε atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => regularizedKernel (ε n) x) atTop (𝓝 (coulombKernel x)) := by
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  have hr := hh.rpow tendsto_const_nhds
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) : ‖x‖^2 ≠ 0 ∨ 0 < (-1/2:ℝ))
  simpa only [regularizedKernel, coulombKernel_eq_rpow] using hr

theorem regularizedKernel_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedKernel (ε n) x*φ x)
      atTop (𝓝 (∫ x, coulombKernel x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => coulombKernel x*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => coulombKernel x*‖φ x‖)
  · intro n
    exact ((contDiff_regularizedKernel (hε n).ne').continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regularizedKernel_le hx) (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedKernel_tendsto hlim hx).mul_const (φ x)

theorem integral_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, coulombKernel x*coordinateLaplacian φ x) = -(4*Real.pi*φ 0) := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hleft := regularizedKernel_integral_tendsto hε hεlim
    (continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)))
    (hasCompactSupport_coordinateLaplacian hφc)
  have hright := (regularizedCharge_tendsto_dirac hε hεlim hφ.continuous hφc).neg
  have he : (fun n => ∫ x, regularizedKernel (ε n) x*coordinateLaplacian φ x) =
      (fun n => -(∫ x, regularizedCharge (ε n) x*φ x)) := by
    funext n
    rw [integral_mul_coordinateLaplacian_eq
      (fun x _ => ((contDiff_regularizedKernel (hε n).ne').of_le
        (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt) hφ hφc]
    simp_rw [laplacian_regularizedKernel (hε n).ne', neg_mul, integral_neg]
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem coordinateLaplacian_translate (φ : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => φ (z+y)) x = coordinateLaplacian φ (x+y) := by
  unfold coordinateLaplacian
  simp only [add_right_comm _ _ y]

theorem integral_translated_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (y : Position) :
    (∫ x, coulombKernel (x-y)*coordinateLaplacian φ x) = -(4*Real.pi*φ y) := by
  have ht : ContDiff ℝ ∞ (fun z => φ (z+y)) := hφ.comp (contDiff_id.add contDiff_const)
  have hc : HasCompactSupport (fun z => φ (z+y)) :=
    hφc.comp_homeomorph (Homeomorph.addRight y)
  have he := integral_coulombKernel_laplacian ht hc
  simp only [coordinateLaplacian_translate, zero_add] at he
  rw [← integral_add_right_eq_self (fun x => coulombKernel (x-y)*coordinateLaplacian φ x) y]
  simpa only [add_sub_cancel_right] using he

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Localization_TruncatedCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma coulombKernel_nonneg (x : Space) : 0 ≤ coulombKernel x := inv_nonneg.mpr (norm_nonneg _)
lemma coulombKernel_measurable : Measurable coulombKernel := measurable_norm.inv
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity, finite L² normalization and compact support of the actual
manufactured planar potential. The differential eigen-equation and gap are
not assumed by these declarations. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarMode_normalized : (∫ r, normalizedPlanarMode r ^ 2) = 1 := by
  simp_rw [normalizedPlanarMode, div_pow]
  rw [integral_div, Real.sq_sqrt planarResolventMode_square_integral_positive.le,
    div_self planarResolventMode_square_integral_positive.ne']

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Gaussian in the transverse direction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem verticalMode_normalized {freq : ℝ} (hfreq : 0 < freq) :
    (∫ z : ℝ, verticalMode freq z ^ 2) = 1 := by
  simp_rw [verticalMode_square hfreq]
  rw [integral_div, integral_gaussian, div_self]
  exact (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)).ne'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual localized modes in planar/transverse coordinates. The measure is
the product of planar Euclidean volume and one-dimensional Lebesgue measure.
The split Laplacian below is the sum of the three coordinate derivatives. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ p, localizedMode freq u p ^ 2) = 1 := by
  simp_rw [localizedMode, mul_pow]
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun r => normalizedPlanarMode (r - u) ^ 2)
      (fun z => verticalMode freq z ^ 2),
    integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized, verticalMode_normalized hfreq, one_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume-preserving planar/transverse coordinates for the actual
three-dimensional Coulomb space. The intermediate product has its Euclidean
L² norm; the final ordinary product carries the same product volume. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_integral (f : SplitPosition → ℝ) :
    (∫ x : Position, f (positionSplitCoordinates x)) = ∫ p, f p :=
  positionSplitCoordinates_measurePreserving.integral_comp
    positionSplitCoordinates.toHomeomorph.measurableEmbedding f

theorem positionSplitCoordinates_norm_sq (x : Position) :
    ‖x‖ ^ 2 = ‖(positionSplitCoordinates x).1‖ ^ 2 +
      (positionSplitCoordinates x).2 ^ 2 := by
  change ‖x‖ ^ 2 = ‖(positionSplitIsometry x).fst‖ ^ 2 + (positionSplitIsometry x).snd ^ 2
  have h := WithLp.prod_norm_sq_eq_of_L2 (positionSplitIsometry x)
  rw [positionSplitIsometry.norm_map] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem continuumLocalizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ x : Position, continuumLocalizedMode freq u x ^ 2) = 1 := by
  change (∫ x : Position, (localizedMode freq u (positionSplitCoordinates x)) ^ 2) = 1
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p ^ 2),
    localizedMode_normalized hfreq]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulomb
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite actual Coulomb interactions of the localized densities. Bounded
probability densities permit the existing elementary near/far Coulomb bound;
no interaction coefficient is introduced as a spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedDensity_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) : 0 < localizedDensity freq u x :=
  sq_pos_of_pos (continuumLocalizedMode_positive hfreq u x)

theorem localizedDensity_mass {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    (∫ x, localizedDensity freq u x) = 1 := continuumLocalizedMode_normalized hfreq u

theorem localizedDensity_coulomb_integrable_bound {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    Integrable (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) ∧
      NeutralAtom.potentialOf (localizedDensity freq u) x ≤ localizedPotentialBound freq := by
  have h := NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x
  simpa only [localizedDensity_mass hfreq u, localizedPotentialBound, NeutralAtom.kernelBallMass,
    NeutralAtom.potentialOf] using h

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedDensity_potential_continuous {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Continuous (NeutralAtom.potentialOf (localizedDensity freq u)) :=
  NeutralAtom.potentialOf_continuous (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u)

theorem localizedCoulombCoeff_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun x => localizedDensity freq u x *
      NeutralAtom.potentialOf (localizedDensity freq v) x) := by
  apply (localizedDensity_integrable hfreq u).mul_bdd (c := localizedPotentialBound freq)
    (localizedDensity_potential_continuous hfreq v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (localizedDensity_potential_nonnegative freq v x)]
    exact (localizedDensity_coulomb_integrable_bound hfreq v x).2)

theorem localizedCoulombCoeff_nonnegative (freq : ℝ) (u v : PlanarPosition) :
    0 ≤ localizedCoulombCoeff freq u v :=
  integral_nonneg (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
    (localizedDensity_potential_nonnegative freq v x))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_Gaussian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma gaussian_pos (a : ℝ) (x : Space) : 0 < gaussian a x := Real.exp_pos _
lemma gaussian_le_one {a : ℝ} (ha : 0 ≤ a) (x : Space) : gaussian a x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg ‖x‖]
lemma gaussian_continuous (a : ℝ) : Continuous (gaussian a) := by unfold gaussian; fun_prop
lemma gaussian_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussian a) := by
  change Integrable (fun x : Space => Real.exp (-a*‖x‖^2))
  have H := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V:=Space)
    (show 0 < (a : ℂ).re from ha) 0 0).re
  change Integrable (fun x : Space => (Complex.exp (-(a:ℂ)*↑‖x‖^2 + 0 * ↑(inner ℝ (0:Space) x))).re) at H
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re, gaussian] using H
lemma gaussian_integral {a : ℝ} (ha : 0 < a) :
    (∫ x, gaussian a x) = (Real.pi/a)^(3/2:ℝ) := by
  simpa [gaussian] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V:=Space) ha
lemma kernel_gaussian_integral {d : Space} (hd : d ≠ 0) :
    ‖d‖⁻¹ = (Real.sqrt Real.pi)⁻¹ * ∫ t : ℝ, gaussian (t^2) d := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  rw [integral_gaussian, Real.sqrt_div (by positivity), Real.sqrt_sq (norm_nonneg _)]
  field_simp

lemma gaussian_product (a : ℝ) (x y z : Space) :
    gaussian (2*a) (x-z)*gaussian (2*a) (y-z) =
      gaussian a (x-y)*gaussian (4*a) (z-(1/2:ℝ) • (x+y)) := by
  unfold gaussian
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2),
    inner_smul_right, inner_add_right]
  rw [mul_pow, norm_add_sq_real]
  rw [real_inner_comm z x, real_inner_comm z y]
  ring

lemma gaussian_product_integrable {a : ℝ} (ha : 0 < a) (x y : Space) :
    Integrable (fun z => gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) := by
  simp_rw [gaussian_product]
  exact ((gaussian_integrable (by positivity : 0 < 4*a)).comp_sub_right _).const_mul _

lemma gaussian_convolution_identity {a : ℝ} (ha : 0 < a) (x y : Space) :
    (∫ z, gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) =
      gaussian a (x-y)*(Real.pi/(4*a))^(3/2:ℝ) := by
  simp_rw [gaussian_product]
  rw [integral_const_mul, integral_sub_right_eq_self, gaussian_integral (by positivity)]

lemma integrable_gaussian_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p : Space × Space => f p.1*f p.2*gaussian a (p.1-p.2)) := by
  apply (hf.norm.mul_prod hf.norm).mono' (by
    apply Measurable.aestronglyMeasurable
    exact ((hm.comp measurable_fst).mul (hm.comp measurable_snd)).mul
      ((gaussian_continuous a).measurable.comp (by fun_prop)))
  exact Filter.Eventually.of_forall (fun p => by
    simp only [norm_mul, Real.norm_of_nonneg (gaussian_pos a _).le]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (gaussian_le_one ha _))

lemma gaussian_square_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
  have hm' : Measurable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
    have h1 : Measurable (fun q : (Space × Space) × Space => f q.1.1*f q.1.2) :=
      (hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))
    apply h1.mul
    exact ((gaussian_continuous _).measurable.comp (by fun_prop)).mul
      ((gaussian_continuous _).measurable.comp (by fun_prop))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => (gaussian_product_integrable ha p.1 p.2).const_mul (f p.1*f p.2))
  · have he (p : Space × Space) :
        (∫ z, ‖(f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))‖) =
          (‖f p.1‖*‖f p.2‖*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
      rw [integral_const_mul, gaussian_convolution_identity ha]
      ring
    simp_rw [he]
    exact (integrable_gaussian_pair hf.norm hm.norm ha.le).mul_const _

lemma gaussian_form_nonneg {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2) := by
  have hi := gaussian_square_integrable hf hm ha
  have H := integral_integral_swap (f := fun (p : Space × Space) (z : Space) =>
    (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) hi
  have hleft (p : Space × Space) :
      (∫ z, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (f p.1*f p.2*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
    rw [integral_const_mul, gaussian_convolution_identity ha]
    ring
  have hright (z : Space) :
      (∫ p : Space × Space, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (∫ x, f x*gaussian (2*a) (x-z))^2 := by
    simp_rw [show ∀ p : Space × Space,
      (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z)) =
      (f p.1*gaussian (2*a) (p.1-z))*(f p.2*gaussian (2*a) (p.2-z)) from fun p => by ring]
    exact (integral_prod_mul (μ:=volume) (ν:=volume)
      (fun x : Space => f x*gaussian (2*a) (x-z))
      (fun x : Space => f x*gaussian (2*a) (x-z))).trans (pow_two _).symm
  simp_rw [hleft, hright] at H
  rw [integral_mul_const] at H
  have hnonneg : 0 ≤ (∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2)) *
      (Real.pi/(4*a))^(3/2:ℝ) := H.symm ▸ integral_nonneg (fun z => sq_nonneg _)
  exact nonneg_of_mul_nonneg_left hnonneg (Real.rpow_pos_of_pos (by positivity) _)
lemma space_ae_distinct : ∀ᵐ p : Space × Space, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall (fun x => by
    rw [ae_iff]
    simp only [not_not]
    have he : {y : Space | x = y} = {x} := by ext y; simp [eq_comm]
    change volume {y : Space | x = y} = 0
    rw [he, measure_singleton])

lemma gaussian_parameter_integrable {d : Space} (hd : d ≠ 0) :
    Integrable (fun t : ℝ => gaussian (t^2) d) := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  exact integrable_exp_neg_mul_sq (sq_pos_of_pos (norm_pos_iff.mpr hd))

lemma gaussian_parameter_integral {d : Space} (hd : d ≠ 0) :
    (∫ t : ℝ, gaussian (t^2) d) = coulombKernel d * Real.sqrt Real.pi := by
  have H := kernel_gaussian_integral hd
  unfold coulombKernel
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    _ = ((Real.sqrt Real.pi)⁻¹*(∫ t : ℝ, gaussian (t^2) d))*Real.sqrt Real.pi := by field_simp
    _ = _ := by rw [← H]

lemma coulomb_gaussian_integrable_of_pair {f : Space → ℝ} (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    Integrable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
  have hm' : Measurable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
    apply ((hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))).mul
    unfold gaussian
    fun_prop
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [space_ae_distinct] with p hp
    exact (gaussian_parameter_integrable (sub_ne_zero.mpr hp)).const_mul (f p.1*f p.2)
  · have hi := hp.norm.mul_const (Real.sqrt Real.pi)
    apply hi.congr
    filter_upwards [space_ae_distinct] with p hp
    simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    simp only [Real.norm_of_nonneg (coulombKernel_nonneg _)]
    ring

lemma coulomb_form_nonneg_of_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2) := by
  have hi := coulomb_gaussian_integrable_of_pair hm hp
  have H := integral_integral_swap (f := fun (p : Space × Space) (t : ℝ) =>
    f p.1*f p.2*gaussian (t^2) (p.1-p.2)) hi
  have hl : (∫ p : Space × Space, ∫ t : ℝ, f p.1*f p.2*gaussian (t^2) (p.1-p.2)) =
      (∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2))*Real.sqrt Real.pi := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [space_ae_distinct] with p hp
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    ring
  rw [hl] at H
  have ht : ∀ᵐ t : ℝ, t ≠ 0 := by rw [ae_iff]; simp
  have hn : 0 ≤ ∫ t : ℝ, ∫ p : Space × Space, f p.1*f p.2*gaussian (t^2) (p.1-p.2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ht] with t ht
    exact gaussian_form_nonneg hf hm (sq_pos_of_ne_zero ht)
  rw [← H] at hn
  exact nonneg_of_mul_nonneg_left hn (Real.sqrt_pos.mpr Real.pi_pos)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_CoulombTest
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_zero {χ : Space → ℝ} {x : Space} (hx : x∉tsupport χ) :
    testCharge χ x=0 := by
  simp only [testCharge,NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hx,neg_zero,zero_div]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_potential {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (y : Space) :
    (∫ x, coulombKernel (y-x)*testCharge χ x)=χ y := by
  have H := NeutralAtom.integral_translated_coulombKernel_laplacian hχ hc y
  have he : (fun x => coulombKernel (y-x)*testCharge χ x)=
      (fun x => -(NeutralAtom.coulombKernel (x-y)*NeutralAtom.coordinateLaplacian χ x)/(4*Real.pi)) := by
    funext x
    simp only [testCharge,coulombKernel,NeutralAtom.coulombKernel,norm_sub_rev]
    ring
  rw [he,integral_div,integral_neg,H]
  field_simp

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global Coulomb pairing for the bounded integrable packets used in
the mode construction. Existing Gaussian-kernel positivity applies directly
once the elementary bounded-density estimate supplies joint integrability. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

namespace CoulombPacket

theorem joint_integrable (f g : CoulombPacket) :
    Integrable (fun p : Position × Position =>
      f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) := by
  have hg (x : Position) := NeutralAtom.bounded_density_convolution
    NeutralAtom.measurable_coulombKernel NeutralAtom.coulombKernel_nonneg
    (NeutralAtom.coulombKernel_integrableOn_ball 1) (fun _ => NeutralAtom.coulombKernel_le_one)
    g.integrable.norm (fun _ => norm_nonneg _) g.bound_spec x
  let C := g.bound * NeutralAtom.kernelBallMass 1 + ∫ y, ‖g y‖
  have hm : Measurable (fun p : Position × Position =>
      f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) :=
    ((f.continuous.measurable.comp measurable_fst).mul
      (g.continuous.measurable.comp measurable_snd)).mul
      (Coulomb.coulombKernel_measurable.comp (measurable_fst.sub measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => by
      have hi := (hg x).1.const_mul ‖f x‖
      apply hi.mono' ((hm.comp ((measurable_const : Measurable (fun _ : Position => x)).prodMk
        measurable_id)).aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only [Function.comp_def, Prod.fst, Prod.snd, id_eq]
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
        change ‖f x‖ * ‖g y‖ * ‖x - y‖⁻¹ ≤ ‖f x‖ * (‖x - y‖⁻¹ * ‖g y‖)
        ring_nf
        exact le_rfl))
  · apply (f.integrable.norm.const_mul C).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun x => by
      have he : (∫ y, ‖f x * g y * Coulomb.coulombKernel (x - y)‖) =
          ‖f x‖ * ∫ y, NeutralAtom.coulombKernel (x - y) * ‖g y‖ := by
        have hp (y : Position) : ‖f x * g y * Coulomb.coulombKernel (x - y)‖ =
            ‖f x‖ * (NeutralAtom.coulombKernel (x - y) * ‖g y‖) := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
          change ‖f x‖ * ‖g y‖ * ‖x - y‖⁻¹ = ‖f x‖ * (‖x - y‖⁻¹ * ‖g y‖)
          ring
        simp_rw [hp, integral_const_mul]
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
      calc
        _ ≤ ‖f x‖ * C := mul_le_mul_of_nonneg_left (hg x).2 (norm_nonneg (f x))
        _ = _ := mul_comm _ _)

theorem pair_nonnegative (f : CoulombPacket) : 0 ≤ pair f f :=
  Coulomb.coulomb_form_nonneg_of_pair f.integrable f.continuous.measurable (joint_integrable f f)

theorem pair_symmetric (f g : CoulombPacket) : pair f g = pair g f := by
  unfold pair
  rw [Measure.volume_eq_prod, integral_prod _ (joint_integrable f g),
    integral_prod _ (joint_integrable g f), integral_integral_swap (joint_integrable f g)]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Coulomb.coulombKernel, norm_sub_rev x y]
  ring

theorem pair_add_left (f g h : CoulombPacket) : pair (add f g) h = pair f h + pair g h := by
  unfold pair
  change (∫ p : Position × Position, (f p.1 + g p.1) * h p.2 * Coulomb.coulombKernel (p.1 - p.2)) = _
  simp_rw [add_mul]
  exact integral_add (joint_integrable f h) (joint_integrable g h)

theorem pair_smul_left (t : ℝ) (f g : CoulombPacket) : pair (smul t f) g = t * pair f g := by
  unfold pair
  change (∫ p : Position × Position, (t * f p.1) * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) = _
  simp_rw [mul_assoc]
  exact integral_const_mul t _

theorem pair_add_right (f g h : CoulombPacket) : pair f (add g h) = pair f g + pair f h := by
  rw [pair_symmetric, pair_add_left, pair_symmetric g f, pair_symmetric h f]

theorem pair_smul_right (t : ℝ) (f g : CoulombPacket) : pair f (smul t g) = t * pair f g := by
  rw [pair_symmetric, pair_smul_left, pair_symmetric g f]

theorem pair_cauchy (f g : CoulombPacket) : pair f g ^ 2 ≤ pair f f * pair g g := by
  have h (t : ℝ) : 0 ≤ pair g g * (t * t) + (2 * pair f g) * t + pair f f := by
    have hn := pair_nonnegative (add f (smul t g))
    rw [pair_add_left, pair_add_right, pair_add_right, pair_smul_left,
      pair_smul_right, pair_smul_right, pair_symmetric g f, pair_smul_left] at hn
    nlinarith only [hn]
  have hd := discrim_le_zero h
  dsimp only [discrim] at hd
  nlinarith only [hd]

end CoulombPacket
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeDecay
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit exponential tail of the actual positive planar mode. Splitting
the Gaussian exponent avoids any assumed asymptotics for a special function. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_double_time (t : ℝ) (b : PlanarPosition) :
    planarHeatKernel t b =
      2 * Real.exp (-‖b‖ ^ 2 / (8 * t)) * planarHeatKernel (2 * t) b := by
  unfold planarHeatKernel
  have h1 : -‖b‖ ^ 2 / (4 * t) = -‖b‖ ^ 2 / (8 * t) + -‖b‖ ^ 2 / (8 * t) := by ring
  have h2 : -‖b‖ ^ 2 / (4 * (2 * t)) = -‖b‖ ^ 2 / (8 * t) := by ring
  rw [h1, h2, Real.exp_add]
  ring

theorem planarHeatForcing_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖)
    (b : PlanarPosition) :
    planarHeatKernel t b * planarForcing (r - b) ≤
      (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t))) * planarHeatKernel (2 * t) b := by
  by_cases hf : planarForcing (r - b) = 0
  · rw [hf, mul_zero]
    exact mul_nonneg (by positivity) (planarHeatKernel_positive (by positivity) b).le
  · have hs : ‖r - b‖ < 1 := lt_of_not_ge
      (fun h => hf (planarForcing_zero_of_norm_ge_one h))
    have hn : ‖r‖ - 1 ≤ ‖b‖ := by
      have htriangle := norm_add_le (r - b) b
      rw [sub_add_cancel] at htriangle
      linarith
    have hsq : (‖r‖ - 1) ^ 2 ≤ ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
    have he : Real.exp (-‖b‖ ^ 2 / (8 * t)) ≤
        Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)) := by
      apply Real.exp_le_exp.mpr
      gcongr
    calc
      _ ≤ planarHeatKernel t b :=
        mul_le_of_le_one_right (planarHeatKernel_positive ht b).le (planarForcing_le_one _)
      _ = 2 * Real.exp (-‖b‖ ^ 2 / (8 * t)) * planarHeatKernel (2 * t) b :=
        planarHeatKernel_double_time t b
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num))
        (planarHeatKernel_positive (by positivity) b).le

theorem planarHeatAverage_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarHeatAverage t r ≤ 2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)) := by
  have hi := (planarHeatKernel_integrable (by positivity : 0 < 2 * t)).const_mul
    (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)))
  have h := integral_mono (planarHeatAverage_integrand_integrable ht r) hi
    (planarHeatForcing_tail ht hr)
  simpa only [integral_const_mul, planarHeatKernel_integral (by positivity : 0 < 2 * t),
    mul_one, planarHeatAverage] using h

theorem planar_heat_tail_exponent {t d : ℝ} (ht : 0 < t) :
    d / 2 ≤ t / 2 + d ^ 2 / (8 * t) := by
  have he : t / 2 + d ^ 2 / (8 * t) - d / 2 = (2 * t - d) ^ 2 / (8 * t) := by
    field_simp
    ring
  have hp : 0 ≤ (2 * t - d) ^ 2 / (8 * t) := by positivity
  linarith

theorem planarHeatResolvent_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    Real.exp (-t) * planarHeatAverage t r ≤
      (2 * Real.exp (-(‖r‖ - 1) / 2)) * Real.exp (-(1 / 2 : ℝ) * t) := by
  have he : -t + (-((‖r‖ - 1) ^ 2) / (8 * t)) ≤ -(‖r‖ - 1) / 2 + -(1 / 2 : ℝ) * t := by
    have hA : (‖r‖ - 1) / 2 ≤ t / 2 + (‖r‖ - 1) ^ 2 / (8 * t) :=
      planar_heat_tail_exponent ht
    rw [neg_div]
    linarith
  calc
    _ ≤ Real.exp (-t) * (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t))) :=
      mul_le_mul_of_nonneg_left (planarHeatAverage_tail ht hr) (Real.exp_pos _).le
    _ = 2 * Real.exp (-t + (-((‖r‖ - 1) ^ 2) / (8 * t))) := by rw [Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-(‖r‖ - 1) / 2 + -(1 / 2 : ℝ) * t) := by gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem planarResolventMode_exponential_tail {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarResolventMode r ≤ 4 * Real.exp (-(‖r‖ - 1) / 2) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)
  rw [planarResolventMode_heat_representation]
  have h := integral_mono_ae (planarResolventMode_heat_integrable r)
    (hi.const_mul (2 * Real.exp (-(‖r‖ - 1) / 2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact planarHeatResolvent_tail ht hr)
  have he : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 / 2 : ℝ) * t)) = 2 := by
    rw [integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
    norm_num
  rw [integral_const_mul, he] at h
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHopping
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive contact hopping integral. Its Lipschitz control is
inherited from the compact forcing through the mass-one resolvent kernel. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem planarAxis_zero_norm : ‖planarAxis 0‖ = 1 := by
  simp [planarAxis]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation/reflection invariance of the actual manufactured planar data.
The hopping between arbitrary translated centers depends only on distance. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarForcing_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (r : PlanarPosition) :
    planarForcing (L r) = planarForcing r := by
  simp only [planarForcing, L.norm_map]

theorem planarResolventKernel_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventKernel (L r) = planarResolventKernel r := by
  simp only [planarResolventKernel, planarResolventIntegrand, planarHeatKernel, L.norm_map]

theorem planarResolventMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventMode (L r) = planarResolventMode r := by
  unfold planarResolventMode
  rw [← MeasureTheory.integral_comp L
    (fun b => planarResolventKernel b * planarForcing (L r - b))]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [planarResolventKernel_isometry, ← L.map_sub, planarForcing_isometry]

theorem normalizedPlanarMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : normalizedPlanarMode (L r) = normalizedPlanarMode r := by
  simp only [normalizedPlanarMode, planarResolventMode_isometry]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPacketTests
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet combinations and the exact global Poisson duality for
smooth compact tests. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

theorem pair_zero_left (f : CoulombPacket) : pair zero f = 0 := by
  simp [pair, zero]

theorem pair_sumList_left (fs : List CoulombPacket) (g : CoulombPacket) :
    pair (sumList fs) g = (fs.map (fun f => pair f g)).sum := by
  induction fs with
  | nil => exact pair_zero_left g
  | cons f fs ih => simp only [sumList, pair_add_left, ih, List.map_cons, List.sum_cons]

theorem pair_combination_left {m : ℕ} (f : Fin m → CoulombPacket) (d : Fin m → ℝ)
    (g : CoulombPacket) : pair (combination f d) g = ∑ i, d i * pair (f i) g := by
  rw [combination, pair_sumList_left, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, pair_smul_left]

theorem pair_combination_right {m : ℕ} (f : CoulombPacket) (g : Fin m → CoulombPacket)
    (d : Fin m → ℝ) : pair f (combination g d) = ∑ j, d j * pair f (g j) := by
  calc
    _ = pair (combination g d) f := pair_symmetric _ _
    _ = ∑ j, d j * pair (g j) f := pair_combination_left g d f
    _ = _ := Finset.sum_congr rfl (fun j _ => congrArg (fun a => d j * a) (pair_symmetric (g j) f))

theorem pair_combinations {m n : ℕ} (f : Fin m → CoulombPacket) (g : Fin n → CoulombPacket)
    (d : Fin m → ℝ) (e : Fin n → ℝ) :
    pair (combination f d) (combination g e) =
      ∑ i, ∑ j, d i * e j * pair (f i) (g j) := by
  rw [pair_combination_left]
  simp_rw [pair_combination_right, Finset.mul_sum, mul_assoc]

theorem pair_test (f : CoulombPacket) (χ : Position → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    pair f (test χ hχ hc) = ∫ x, f x * χ x := by
  unfold pair
  rw [Measure.volume_eq_prod, integral_prod _ (joint_integrable f (test χ hχ hc))]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ y, f x * Coulomb.testCharge χ y * Coulomb.coulombKernel (x - y)) = _
  rw [show (fun y => f x * Coulomb.testCharge χ y * Coulomb.coulombKernel (x - y)) =
      (fun y => f x * (Coulomb.coulombKernel (x - y) * Coulomb.testCharge χ y)) by funext y; ring,
    integral_const_mul, Coulomb.testCharge_potential hχ hc]

theorem test_pair_test (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ) :
    pair (test χ hχ hcχ) (test ψ hψ hcψ) = ∫ x, Coulomb.testCharge χ x * ψ x :=
  pair_test _ _ hψ hcψ

theorem test_pair_orthogonal (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ)
    (hd : Disjoint (tsupport χ) (tsupport ψ)) : pair (test χ hχ hcχ) (test ψ hψ hcψ) = 0 := by
  rw [test_pair_test]
  have hz (x : Position) : Coulomb.testCharge χ x * ψ x = 0 := by
    by_cases hx : x ∈ tsupport χ
    · rw [image_eq_zero_of_notMem_tsupport (fun hy => Set.disjoint_left.mp hd hx hy), mul_zero]
    · rw [Coulomb.testCharge_zero hx, zero_mul]
  simp_rw [hz, integral_zero]

end ContinuumCoulomb.CoulombPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPacketCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global Coulomb coercivity from disjoint compact tests and approximate
local duality. All integrals range over the whole Euclidean space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

theorem test_combination_energy {m : ℕ} (χ : Fin m → Position → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hc : ∀ i, HasCompactSupport (χ i))
    (hd : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K : ℝ} (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (d : Fin m → ℝ) :
    pair (combination (fun i => test (χ i) (hχ i) (hc i)) d)
      (combination (fun i => test (χ i) (hχ i) (hc i)) d) ≤ K * ∑ i, d i ^ 2 := by
  classical
  rw [pair_combinations]
  have hentry (i j : Fin m) : pair (test (χ i) (hχ i) (hc i)) (test (χ j) (hχ j) (hc j)) =
      if i = j then ∫ x, Coulomb.testCharge (χ i) x * χ i x else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true, if_true] using test_pair_test (χ i) (χ i) (hχ i) (hχ i) (hc i) (hc i)
    · rw [ite_eq_right hij]
      exact test_pair_orthogonal (χ i) (χ j) (hχ i) (hχ j) (hc i) (hc j) (hd i j hij)
  simp_rw [hentry]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  calc
    _ ≤ ∑ i, d i ^ 2 * K := Finset.sum_le_sum (fun i _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg (d i)))
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

theorem gram_coercive_of_dual_lower {m : ℕ} (f : Fin m → CoulombPacket)
    (χ : Fin m → Position → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hc : ∀ i, HasCompactSupport (χ i))
    (hd : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K a : ℝ} (hK : 0 < K) (ha : 0 ≤ a)
    (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (hdual : ∀ d : Fin m → ℝ, a * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, d i * d j * ∫ x, f i x * χ j x)
    (d : Fin m → ℝ) :
    (a ^ 2 / K) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, pair (f i) (f j) * d i * d j := by
  let ρ := combination f d
  let η := combination (fun i => test (χ i) (hχ i) (hc i)) d
  let S := ∑ i, d i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hpair : a * S ≤ pair ρ η := by
    rw [pair_combinations]
    simp_rw [pair_test]
    exact hdual d
  have hpair0 : 0 ≤ pair ρ η := (mul_nonneg ha hS).trans hpair
  have hsquare : (a * S) ^ 2 ≤ pair ρ η ^ 2 :=
    (sq_le_sq₀ (mul_nonneg ha hS) hpair0).mpr hpair
  have htest := test_combination_energy χ hχ hc hd henergy d
  have hQ : 0 ≤ pair ρ ρ := pair_nonnegative ρ
  have hbound : (a * S) ^ 2 ≤ pair ρ ρ * (K * S) :=
    hsquare.trans ((pair_cauchy ρ η).trans (mul_le_mul_of_nonneg_left htest hQ))
  have hcoercive : (a ^ 2 / K) * S ≤ pair ρ ρ := by
    by_cases hz : S = 0
    · simpa only [hz, mul_zero] using hQ
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
      have hcancel := (mul_le_mul_iff_left₀ hSpos).mp
        (show (a ^ 2 * S) * S ≤ (pair ρ ρ * K) * S by nlinarith only [hbound])
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hK).mpr hcancel
  change (a ^ 2 / K) * S ≤ pair (combination f d) (combination f d) at hcoercive
  rw [pair_combinations] at hcoercive
  convert hcoercive using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ContinuumCoulomb.CoulombPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombGramApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative local duality for overlapping densities. The compact local
tests are disjoint; the electron density packets need not be disjoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_lower {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, a ≤ A i i)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (a - m * delta) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, A i j * d i * d j := by
  classical
  have hpoint (i j : Fin m) :
      (if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2) ≤
        A i j * d i * d j := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have h := mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (d i))
      have hzero := mul_nonneg hdelta (sq_nonneg (d i))
      nlinarith
    · rw [ite_eq_right hij, zero_sub]
      have hprod : |A i j * d i * d j| ≤ delta * (|d i| * |d j|) := by
        calc
          _ = |A i j| * (|d i| * |d j|) := by simp only [abs_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hoff i j hij)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have htwo : 2 * (|d i| * |d j|) ≤ d i ^ 2 + d j ^ 2 := by
        nlinarith [sq_nonneg (|d i| - |d j|), sq_abs (d i), sq_abs (d j)]
      have hscaled := mul_le_mul_of_nonneg_left htwo hdelta
      nlinarith [neg_abs_le (A i j * d i * d j)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpoint i j
  have hrow (i : Fin m) :
      (∑ j, ((if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2))) =
      a * d i ^ 2 - delta / 2 * ((m : ℝ) * d i ^ 2 + ∑ j, d j ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hrow] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombSymmetry
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual strict positivity and symmetry of the direct Coulomb coefficients. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedCoulomb_product_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun p : Position × Position => localizedDensity freq u p.1 *
      (NeutralAtom.coulombKernel (p.1 - p.2) * localizedDensity freq v p.2))
      ((volume : Measure Position).prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : Position × Position => localizedDensity freq u p.1 *
        (NeutralAtom.coulombKernel (p.1 - p.2) * localizedDensity freq v p.2))
      ((volume : Measure Position).prod volume) :=
    (((localizedDensity_continuous freq u).measurable.comp measurable_fst).mul
      ((NeutralAtom.measurable_coulombKernel.comp (measurable_fst.sub measurable_snd)).mul
        ((localizedDensity_continuous freq v).measurable.comp measurable_snd))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x =>
      (localizedDensity_coulomb_integrable_bound hfreq v x).1.const_mul
        (localizedDensity freq u x))
  · have hn (x y : Position) :
        ‖localizedDensity freq u x *
          (NeutralAtom.coulombKernel (x - y) * localizedDensity freq v y)‖ =
        localizedDensity freq u x *
          (NeutralAtom.coulombKernel (x - y) * localizedDensity freq v y) :=
      Real.norm_of_nonneg (mul_nonneg (localizedDensity_nonnegative freq u x)
        (mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
          (localizedDensity_nonnegative freq v y)))
    simp_rw [hn, integral_const_mul]
    exact localizedCoulombCoeff_integrable hfreq u v

theorem localizedCoulombCoeff_symmetric {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) : localizedCoulombCoeff freq u v = localizedCoulombCoeff freq v u := by
  unfold localizedCoulombCoeff NeutralAtom.potentialOf
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (localizedCoulomb_product_integrable hfreq u v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [NeutralAtom.coulombKernel, norm_sub_rev x y]
      ring))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct Coulomb coefficients as actual translated-density profiles. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarCenter_norm (u : PlanarPosition) : ‖planarCenter u‖ = ‖u‖ := by
  have h := positionSplitCoordinates_norm_sq (planarCenter u)
  simp only [planarCenter, ContinuousLinearEquiv.apply_symm_apply, zero_pow (by norm_num : 2 ≠ 0),
    add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem planarCenter_sub (u v : PlanarPosition) : planarCenter (u - v) = planarCenter u - planarCenter v := by
  change positionSplitCoordinates.symm (u - v, 0) =
    positionSplitCoordinates.symm (u, 0) - positionSplitCoordinates.symm (v, 0)
  rw [← map_sub]
  simp only [Prod.mk_sub_mk, sub_self]

theorem planarCenter_norm_sub (u v : PlanarPosition) : ‖planarCenter u - planarCenter v‖ = ‖u - v‖ := by
  rw [← planarCenter_sub, planarCenter_norm]

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

theorem localizedDensity_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x = localizedDensity freq 0 (x - planarCenter u) := by
  simp only [localizedDensity, continuumLocalizedMode_translate freq u]

theorem localizedDensity_potential_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq u) x =
      NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) := by
  unfold NeutralAtom.potentialOf
  rw [← integral_add_right_eq_self
    (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) (planarCenter u)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [localizedDensity_translate freq u, add_sub_cancel_right]
    congr 2
    abel)

theorem localizedCoulombProfileAt_eq (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombCoeff freq 0 u := by
  unfold localizedCoulombProfileAt localizedCoulombCoeff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z => localizedDensity freq 0 x * z)
      (localizedDensity_potential_translate freq u x).symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombRadial
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual direct Coulomb interaction depends only on planar separation. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem liftPlanarIsometry_coordinates (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (x : Position) :
    positionSplitCoordinates (liftPlanarIsometry L x) =
      (L (positionSplitCoordinates x).1, (positionSplitCoordinates x).2) := by
  change WithLp.ofLp (positionSplitIsometry (positionSplitIsometry.symm
    ((LinearIsometryEquiv.withLpProdCongr 2 L (LinearIsometryEquiv.refl ℝ ℝ))
      (positionSplitIsometry x)))) = _
  rw [positionSplitIsometry.apply_symm_apply]
  rfl

theorem localizedDensity_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    localizedDensity freq (L u) (liftPlanarIsometry L x) = localizedDensity freq u x := by
  simp only [localizedDensity, continuumLocalizedMode, localizedMode,
    liftPlanarIsometry_coordinates, ← L.map_sub, normalizedPlanarMode_isometry]

theorem localizedDensity_potential_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq (L u)) (liftPlanarIsometry L x) =
      NeutralAtom.potentialOf (localizedDensity freq u) x := by
  unfold NeutralAtom.potentialOf
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun y => NeutralAtom.coulombKernel (liftPlanarIsometry L x - y) * localizedDensity freq (L u) y)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [localizedDensity_liftPlanarIsometry, ← (liftPlanarIsometry L).map_sub]
  simp only [NeutralAtom.coulombKernel, LinearIsometryEquiv.norm_map]

theorem localizedCoulombCoeff_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u v : PlanarPosition) :
    localizedCoulombCoeff freq (L u) (L v) = localizedCoulombCoeff freq u v := by
  unfold localizedCoulombCoeff
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun x => localizedDensity freq (L u) x * NeutralAtom.potentialOf (localizedDensity freq (L v)) x)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_liftPlanarIsometry, localizedDensity_potential_liftPlanarIsometry]

theorem localizedCoulombProfileAt_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) :
    localizedCoulombProfileAt freq (L u) = localizedCoulombProfileAt freq u := by
  rw [localizedCoulombProfileAt_eq, localizedCoulombProfileAt_eq]
  simpa only [map_zero] using localizedCoulombCoeff_isometry freq L 0 u

theorem localizedCoulombProfileAt_norm (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombProfile freq ‖u‖ := by
  have hn : ‖‖u‖ • planarAxis 0‖ = ‖u‖ := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (norm_nonneg u)]
  have h := localizedCoulombProfileAt_isometry freq
    ((ℝ ∙ (‖u‖ • planarAxis 0 - u))ᗮ.reflection) (‖u‖ • planarAxis 0)
  rw [Submodule.reflection_sub hn] at h
  exact h

theorem localizedCoulombCoeff_displacement (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfileAt freq (v - u) := by
  unfold localizedCoulombCoeff localizedCoulombProfileAt
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x)
    (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right, localizedDensity_potential_translate freq v]
  congr 2
  rw [planarCenter_sub]
  abel

theorem localizedCoulombCoeff_distance (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfile freq ‖u - v‖ := by
  rw [localizedCoulombCoeff_displacement, localizedCoulombProfileAt_norm, norm_sub_rev]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLeakage
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential off-site density leakage for the actual localized modes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_fst_norm_le (x : Position) :
    ‖(positionSplitCoordinates x).1‖ ≤ ‖x‖ := by
  have h := positionSplitCoordinates_norm_sq x
  nlinarith [sq_nonneg (positionSplitCoordinates x).2, norm_nonneg x,
    norm_nonneg (positionSplitCoordinates x).1]

theorem continuumLocalizedMode_planar_tail {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) (hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖) :
    continuumLocalizedMode freq u x ≤ 4 * localizedAmplitudeBound freq *
      Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) := by
  have hp := div_le_div_of_nonneg_right (planarResolventMode_exponential_tail hr)
    (Real.sqrt_nonneg (∫ r, planarResolventMode r ^ 2))
  have hv : verticalMode freq (positionSplitCoordinates x).2 ≤
      1 / Real.sqrt (Real.sqrt (Real.pi / freq)) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (positionSplitCoordinates x).2])
  change (planarResolventMode ((positionSplitCoordinates x).1 - u) /
    Real.sqrt (∫ r, planarResolventMode r ^ 2)) * verticalMode freq (positionSplitCoordinates x).2 ≤ _
  calc
    _ ≤ (4 * Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) /
        Real.sqrt (∫ r, planarResolventMode r ^ 2)) *
          (1 / Real.sqrt (Real.sqrt (Real.pi / freq))) :=
      mul_le_mul hp hv (verticalMode_positive hfreq _).le (by positivity)
    _ = _ := by unfold localizedAmplitudeBound; ring

theorem localizedTailConstant_nonnegative (freq : ℝ) : 0 ≤ localizedTailConstant freq :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem localizedDensity_planar_tail {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) (hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖) :
    localizedDensity freq u x ≤ localizedTailConstant freq *
      Real.exp (-‖(positionSplitCoordinates x).1 - u‖) := by
  have h := (sq_le_sq₀ (continuumLocalizedMode_positive hfreq u x).le
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (localizedAmplitudeBound_positive hfreq).le) (Real.exp_pos _).le)).mpr
    (continuumLocalizedMode_planar_tail hfreq u x hr)
  have he : Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) ^ 2 =
      Real.exp 1 * Real.exp (-‖(positionSplitCoordinates x).1 - u‖) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, he] at h
  simpa only [localizedDensity, localizedTailConstant, mul_assoc] using h

theorem localizedDensity_near_other_center {freq R : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) (hx : ‖x - planarCenter v‖ ≤ R)
    (hsep : R + 1 ≤ ‖u - v‖) :
    localizedDensity freq u x ≤ localizedTailConstant freq * Real.exp (R - ‖u - v‖) := by
  have hp : ‖(positionSplitCoordinates x).1 - v‖ ≤ R := by
    have h := (positionSplitCoordinates_fst_norm_le (x - planarCenter v)).trans hx
    simpa only [map_sub, planarCenter, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub] using h
  have ht : ‖u - v‖ ≤ ‖u - (positionSplitCoordinates x).1‖ +
      ‖(positionSplitCoordinates x).1 - v‖ := by
    simpa only [dist_eq_norm] using dist_triangle u (positionSplitCoordinates x).1 v
  rw [norm_sub_rev u (positionSplitCoordinates x).1] at ht
  have hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖ := by linarith
  exact (localizedDensity_planar_tail hfreq u x hr).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDuality
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact local dual tests: a common positive diagonal mass,
disjoint supports and exponentially small off-site pairings. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem localizedTest_smooth {χ : Position → ℝ} (hχ : ContDiff ℝ ∞ χ) (u : PlanarPosition) :
    ContDiff ℝ ∞ (localizedTest χ u) := hχ.comp (contDiff_id.sub contDiff_const)

theorem localizedTest_hasCompactSupport {χ : Position → ℝ} (hc : HasCompactSupport χ)
    (u : PlanarPosition) : HasCompactSupport (localizedTest χ u) :=
  hc.comp_homeomorph (Homeomorph.subRight (planarCenter u))

theorem localizedTest_support {χ : Position → ℝ} {R : ℝ}
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (u : PlanarPosition) :
    tsupport (localizedTest χ u) ⊆ Metric.closedBall (planarCenter u) R := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  have hχx : χ (x - planarCenter u) ≠ 0 := hx
  have h := hs (subset_tsupport χ hχx)
  simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using h

theorem localizedTest_disjoint {χ : Position → ℝ} {R : ℝ}
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (u v : PlanarPosition)
    (hsep : 2 * R < ‖u - v‖) : Disjoint (tsupport (localizedTest χ u)) (tsupport (localizedTest χ v)) := by
  apply Set.disjoint_left.mpr
  intro x hxu hxv
  have hu := localizedTest_support hs u hxu
  have hv := localizedTest_support hs v hxv
  simp only [Metric.mem_closedBall, dist_eq_norm] at hu hv
  have h : ‖planarCenter u - planarCenter v‖ ≤ ‖planarCenter u - x‖ + ‖x - planarCenter v‖ := by
    simpa only [dist_eq_norm] using dist_triangle (planarCenter u) x (planarCenter v)
  rw [norm_sub_rev (planarCenter u) x, planarCenter_norm_sub] at h
  linarith

theorem localizedDualPair_diagonal (freq : ℝ) (u : PlanarPosition) (χ : Position → ℝ) :
    localizedDualPair freq u u χ = ∫ x, localizedDensity freq 0 x * χ x := by
  unfold localizedDualPair localizedTest
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * χ (x - planarCenter u)) (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right]

theorem localizedDualPair_diagonal_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) {χ : Position → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hn : ∀ x, 0 ≤ χ x) (h0 : 0 < χ 0) : 0 < localizedDualPair freq u u χ := by
  rw [localizedDualPair_diagonal]
  exact integral_pos_of_integrable_nonneg_nonzero
    ((localizedDensity_continuous freq 0).mul hχ)
    (((localizedDensity_continuous freq 0).mul hχ).integrable_of_hasCompactSupport hc.mul_left)
    (fun x => mul_nonneg (localizedDensity_nonnegative freq 0 x) (hn x))
    (mul_pos (localizedDensity_positive hfreq 0 0) h0).ne'

theorem localizedDualPair_offsite {freq R : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) {χ : Position → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (hsep : R + 1 ≤ ‖u - v‖) :
    |localizedDualPair freq u v χ| ≤
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)) * (∫ x, |χ x|) := by
  have hpt (x : Position) : ‖localizedDensity freq u (x + planarCenter v) * χ x‖ ≤
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)) * |χ x| := by
    by_cases hx : χ x = 0
    · simp only [hx, mul_zero, norm_zero, abs_zero, le_refl]
    have hn : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hs (subset_tsupport χ hx)
    have hb := localizedDensity_near_other_center hfreq u v (x + planarCenter v)
      (by simpa only [add_sub_cancel_right] using hn) hsep
    rw [norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq u _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  unfold localizedDualPair localizedTest
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * χ (x - planarCenter v)) (planarCenter v)]
  simp only [add_sub_cancel_right]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq u (x + planarCenter v) * χ x)
    ((hχ.integrable_of_hasCompactSupport (μ := volume) hc).norm.const_mul
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, Real.norm_eq_abs] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDualMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete compact bumps supply local duality for the actual mode densities. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem localDualBump_smooth : ContDiff ℝ ∞ (localDualBump : Position → ℝ) :=
  localDualBump.contDiff

theorem localDualBump_support : tsupport (localDualBump : Position → ℝ) ⊆ Metric.closedBall 0 2 := by
  rw [localDualBump.tsupport_eq]
  exact Set.Subset.rfl

theorem localDualMass_positive {freq : ℝ} (hfreq : 0 < freq) : 0 < localDualMass freq := by
  have h0 : localDualBump (0 : Position) = 1 :=
    localDualBump.one_of_mem_closedBall (by simp [localDualBump])
  have h := localizedDualPair_diagonal_positive hfreq 0 localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump.nonneg' (by rw [h0]; norm_num)
  simpa only [localizedDualPair_diagonal, localDualMass] using h

theorem localLeakageBound_nonnegative (freq D : ℝ) : 0 ≤ localLeakageBound freq D :=
  mul_nonneg (mul_nonneg (localizedTailConstant_nonnegative freq) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

theorem localDualPair_offsite {freq D : ℝ} (hfreq : 0 < freq) (hD : 3 ≤ D)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    |localizedDualPair freq u v localDualBump| ≤ localLeakageBound freq D := by
  have h := localizedDualPair_offsite hfreq u v localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump_support (by linarith : (2 : ℝ) + 1 ≤ ‖u - v‖)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq)) (integral_nonneg (fun _ => abs_nonneg _)))

theorem localDualTests_disjoint {D : ℝ} (hD : 5 ≤ D)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    Disjoint (tsupport (localizedTest localDualBump u)) (tsupport (localizedTest localDualBump v)) :=
  localizedTest_disjoint localDualBump_support u v (by linarith)

theorem localizedDualMatrix_lower {freq D : ℝ} (hfreq : 0 < freq) (hD : 3 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (s : Fin m → ℝ) :
    (localDualMass freq - m * localLeakageBound freq D) * ∑ i, s i ^ 2 ≤
      ∑ i, ∑ j, localizedDualPair freq (u i) (u j) localDualBump * s i * s j := by
  apply dualMatrix_quadratic_lower _ (localLeakageBound_nonnegative freq D)
  · intro i
    rw [localizedDualPair_diagonal]
    exact le_rfl
  · intro i j hij
    exact localDualPair_offsite hfreq hD (u i) (u j) (hsep i j hij)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coercivity of the actual full Coulomb Gram matrix of the localized
resolvent--Gaussian modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem localizedPacket_pair {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    CoulombPacket.pair (localizedPacket hfreq u) (localizedPacket hfreq v) =
      localizedCoulombCoeff freq u v := by
  unfold CoulombPacket.pair localizedCoulombCoeff NeutralAtom.potentialOf
  rw [Measure.volume_eq_prod, integral_prod _ (CoulombPacket.joint_integrable _ _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change localizedDensity freq u x * localizedDensity freq v y * ‖x - y‖⁻¹ =
    localizedDensity freq u x * (‖x - y‖⁻¹ * localizedDensity freq v y)
  ring

theorem testCharge_localizedTest (χ : Position → ℝ) (u : PlanarPosition) (x : Position) :
    Coulomb.testCharge (localizedTest χ u) x = Coulomb.testCharge χ (x - planarCenter u) := by
  unfold Coulomb.testCharge localizedTest
  simp only [sub_eq_add_neg, NeutralAtom.coordinateLaplacian_translate]

theorem localizedTest_energy (χ : Position → ℝ) (u : PlanarPosition) :
    (∫ x, Coulomb.testCharge (localizedTest χ u) x * localizedTest χ u x) =
      ∫ x, Coulomb.testCharge χ x * χ x := by
  simp_rw [testCharge_localizedTest]
  exact integral_sub_right_eq_self (fun x => Coulomb.testCharge χ x * χ x) (planarCenter u)

theorem localDualEnergyBound_positive : 0 < localDualEnergyBound := by
  unfold localDualEnergyBound
  positivity

theorem localizedGram_coercive {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hmargin : 0 ≤ localDualMass freq - m * localLeakageBound freq D) (d : Fin m → ℝ) :
    ((localDualMass freq - m * localLeakageBound freq D) ^ 2 / localDualEnergyBound) *
      ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  have h := CoulombPacket.gram_coercive_of_dual_lower (fun i => localizedPacket hfreq (u i))
    (fun i => localizedTest localDualBump (u i))
    (fun i => localizedTest_smooth localDualBump_smooth (u i))
    (fun i => localizedTest_hasCompactSupport localDualBump.hasCompactSupport (u i))
    (fun i j hij => localDualTests_disjoint hD (u i) (u j) (hsep i j hij))
    localDualEnergyBound_positive hmargin ?_ ?_ d
  · simpa only [localizedPacket_pair] using h
  · intro i
    rw [localizedTest_energy]
    exact (le_abs_self _).trans (by unfold localDualEnergyBound; linarith)
  · intro e
    have he := localizedDualMatrix_lower hfreq (by linarith : (3 : ℝ) ≤ D) u hsep e
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change e i * e j * localizedDualPair freq (u i) (u j) localDualBump = _
    ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGramConstants
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive coercivity constant once the total off-site leakage is
at most half the common diagonal dual mass. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedGramConstant_positive {freq : ℝ} (hfreq : 0 < freq) :
    0 < localizedGramConstant freq :=
  div_pos (sq_pos_of_pos (localDualMass_positive hfreq))
    (mul_pos (by norm_num) localDualEnergyBound_positive)

theorem localizedGram_uniform_coercive {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : m * localLeakageBound freq D ≤ localDualMass freq / 2) (d : Fin m → ℝ) :
    localizedGramConstant freq * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  have ha := localDualMass_positive hfreq
  have hb : localDualMass freq / 2 ≤ localDualMass freq - m * localLeakageBound freq D := by linarith
  have hmargin : 0 ≤ localDualMass freq - m * localLeakageBound freq D := by linarith
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ localDualMass freq / 2) hmargin).mpr hb
  have hc : localizedGramConstant freq ≤
      (localDualMass freq - m * localLeakageBound freq D) ^ 2 / localDualEnergyBound := by
    calc
      _ = (localDualMass freq / 2) ^ 2 / localDualEnergyBound := by
        unfold localizedGramConstant
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hs localDualEnergyBound_positive.le
  exact (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun i _ => sq_nonneg (d i)))).trans
    (localizedGram_coercive hfreq hD u hsep hmargin d)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGramSpacing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed logarithmic spacing controls the total leakage for every
polynomial number of sites. The exponent is chosen once for the reduction. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localLeakageBound_log (freq : ℝ) (k : ℕ) {N : ℝ} (hN : 0 < N) :
    localLeakageBound freq ((k : ℝ) * Real.log N) = localLeakageConstant freq / N ^ k := by
  unfold localLeakageBound localLeakageConstant
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hN]
  ring

theorem exists_localizedGram_spacing {freq : ℝ} (hfreq : 0 < freq) (A : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      5 ≤ (k : ℝ) * Real.log N ∧
      N ^ A * localLeakageBound freq ((k : ℝ) * Real.log N) ≤ localDualMass freq / 2 := by
  let C := localLeakageConstant freq
  let a := localDualMass freq
  have ha : 0 < a := localDualMass_positive hfreq
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨q, hq⟩ := exists_nat_ge (max (5 / Real.log 2) (2 * C / a))
  have hqD : 5 / Real.log 2 ≤ (q : ℝ) := (le_max_left _ _).trans hq
  have hqC : 2 * C / a ≤ (q : ℝ) := (le_max_right _ _).trans hq
  have hqpos : (0 : ℝ) < q := (div_pos (by norm_num) hlog).trans_le hqD
  have hqNat : 0 < q := by exact_mod_cast hqpos
  have hpow : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  refine ⟨A + q, by omega, fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hD := (div_le_iff₀ hlog).mp hqD
  have hqN : (2 : ℝ) ^ q ≤ N ^ q := pow_le_pow_left₀ (by norm_num) hN q
  have hC : 2 * C ≤ a * N ^ q := by
    have h := (div_le_iff₀ ha).mp (hqC.trans (hpow.trans hqN))
    nlinarith only [h]
  constructor
  · have h := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg q)
    have hadd := mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg (by linarith : 1 ≤ N))
    push_cast
    nlinarith only [hD, h, hadd]
  · rw [localLeakageBound_log freq (A + q) hNp, pow_add]
    have hcancel : N ^ A * (C / (N ^ A * N ^ q)) = C / N ^ q := by
      field_simp [pow_ne_zero A hNp.ne', pow_ne_zero q hNp.ne']
    change N ^ A * (C / (N ^ A * N ^ q)) ≤ a / 2
    rw [hcancel]
    apply (div_le_iff₀ (pow_pos hNp q)).mpr
    nlinarith only [hC]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform contact calibration for the actual Coulomb profile, with a
single polynomial scale also enforcing the many-site Gram bound. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCoulombProfile_nonnegative (freq d : ℝ) : 0 ≤ localizedCoulombProfile freq d := by
  unfold localizedCoulombProfile
  rw [localizedCoulombProfileAt_eq]
  exact localizedCoulombCoeff_nonnegative freq _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialConstantBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed positive analytic constants fit uniform polynomial ranges for
every size parameter at least two. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_polynomial_constant_bounds {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∃ q : ℕ, 0 < q ∧ ∀ N : ℝ, 2 ≤ N → (N ^ q)⁻¹ ≤ c ∧ C ≤ N ^ q := by
  obtain ⟨q, hq⟩ := exists_nat_ge (max 1 (max (1 / c) C))
  have hq₁ : (1 : ℝ) ≤ q := (le_max_left _ _).trans hq
  have hqc : 1 / c ≤ (q : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  have hqC : C ≤ (q : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  have hpow : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  refine ⟨q, by exact_mod_cast (by linarith : (0 : ℝ) < q), fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hp := hpow.trans (pow_le_pow_left₀ (by norm_num) hN q)
  refine ⟨?_, hqC.trans hp⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (pow_pos hNp q)).mpr
  have h := (div_le_iff₀ hc).mp (hqc.trans hp)
  nlinarith only [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibrationMesh
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact compatibility between polynomial hopping amplification and the
equal masses of the unit-nucleus Gauss mesh. -/

namespace ContinuumCoulomb.CalibrationMesh

theorem base_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ base n := by
  exact (by norm_num : 2 ≤ 2^30).trans (Nat.pow_le_pow_left hn 30)

end ContinuumCoulomb.CalibrationMesh

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactExtent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact realization preserves polynomial coordinate extent. -/

noncomputable section
namespace ContinuumCoulomb

namespace ContactMediator

theorem globalSite_card (d : SquareLatticeHeisenberg) :
    Fintype.card (GlobalSite d) = d.vertices + 18 * d.edges := by
  simp only [GlobalSite, Fintype.card_fin]
  ring

end ContactMediator
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHubbard
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized direct Coulomb matrix satisfies the full charge
penalty condition used by the complete half-filled Hubbard comparison. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedOffsiteCoulomb_diagonal {m : ℕ} (freq : ℝ) (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedOffsiteCoulomb freq u i i = 0 := by simp [localizedOffsiteCoulomb]

theorem localizedOffsiteCoulomb_symmetric {m : ℕ} {freq : ℝ} (hfreq : 0 < freq)
    (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedOffsiteCoulomb freq u i j = localizedOffsiteCoulomb freq u j i := by
  simp only [localizedOffsiteCoulomb, eq_comm]
  rw [localizedCoulombCoeff_symmetric hfreq]

theorem localizedCoulomb_diagonal_split {m : ℕ} (freq : ℝ) (u : Fin m → PlanarPosition)
    (d : Fin m → ℝ) :
    (∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j) =
      localizedCoulombProfile freq 0 * ∑ i, d i ^ 2 +
        ∑ i, ∑ j, localizedOffsiteCoulomb freq u i j * d i * d j := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ j, ((if i = j then localizedCoulombProfile freq 0 * d i ^ 2 else 0) +
        localizedOffsiteCoulomb freq u i j * d i * d j) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [ite_true, if_true, localizedOffsiteCoulomb_diagonal, zero_mul, add_zero,
          localizedCoulombCoeff_distance, sub_self, norm_zero, pow_two]
        ring
      · simp only [ite_eq_right hij, localizedOffsiteCoulomb, zero_add]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

theorem localizedCoulomb_charge_condition {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : m * localLeakageBound freq D ≤ localDualMass freq / 2) (d : Fin m → ℝ) :
    localizedGramConstant freq * ∑ i, d i ^ 2 ≤
      localizedCoulombProfile freq 0 * ∑ i, d i ^ 2 +
        ∑ i, ∑ j, localizedOffsiteCoulomb freq u i j * d i * d j := by
  rw [← localizedCoulomb_diagonal_split]
  exact localizedGram_uniform_coercive hfreq hD u hsep hleak d

namespace HubbardGlobal

theorem localized_hubbard_Heisenberg {Edge : Type*} [Fintype Edge]
    {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D) (m : ℕ)
    (u : Fin (m + 1) → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : (m + 1 : ℕ) * localLeakageBound freq D ≤ localDualMass freq / 2)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hcal : ∀ e, t e ^ 2 = J e *
      (localizedCoulombProfile freq 0 - localizedCoulombCoeff freq (u (left e)) (u (right e))))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |t e| ≤ epsilon * localizedGramConstant freq) :
    |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t - graphSourceBottom m left right J| ≤
      2 * localizedGramConstant freq * epsilon ^ 3 := by
  apply hubbardFermionBottom_Gram_Heisenberg m (localizedCoulombProfile freq 0)
    (localizedGramConstant freq) (localizedOffsiteCoulomb freq u)
    (localizedOffsiteCoulomb_symmetric hfreq u) (localizedOffsiteCoulomb_diagonal freq u)
    (localizedGramConstant_positive hfreq) (localizedCoulomb_charge_condition hfreq hD u hsep hleak)
    left right t J hloop hsimple ?_ hepsilon hsmall ht
  intro e
  simpa only [localizedOffsiteCoulomb, ite_eq_right (hloop e)] using hcal e

end HubbardGlobal
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFrequency
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frequency evaluated by the literal programs satisfies exactly the
oscillator/slab relation and lies in the uniform spectral-gap regime. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufactured_frequency_ge_one {rho : ℕ} (hrho : 0 < rho) :
    1 ≤ GaussianFrequency.frequency rho := by
  have hr : (1:ℝ) ≤ rho := by exact_mod_cast Nat.succ_le_iff.mpr hrho
  have hp : (1:ℝ) ≤ 4*Real.pi := by linarith [Real.pi_gt_three]
  unfold GaussianFrequency.frequency
  apply Real.le_sqrt_of_sq_le
  simpa only [one_mul,one_pow] using mul_le_mul hp hr (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ 4*Real.pi)

theorem manufactured_frequency_positive {rho : ℕ} (hrho : 0 < rho) :
    0 < GaussianFrequency.frequency rho := lt_of_lt_of_le zero_lt_one (manufactured_frequency_ge_one hrho)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceCoefficientRounding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact common-denominator source coefficient rounding, implemented by
actual integer/rational machine arithmetic. Nonzero rounded weights have
an inverse-polynomial lower bound without assuming one for the source. -/

namespace ContinuumCoulomb.SourceCoefficientRounding
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem coefficient_error {M : ℕ} (hM : 0 < M) (q : ℚ) :
    |q - coefficient M q| ≤ 1 / (2 * (M : ℚ)) := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have heq : q - coefficient M q = ((M : ℚ) * q - round ((M : ℚ) * q)) / M := by
    unfold coefficient
    field_simp
  rw [heq, abs_div, abs_of_pos hm]
  calc
    _ ≤ (1 / 2 : ℚ) / M := div_le_div_of_nonneg_right (abs_sub_round ((M : ℚ) * q)) hm.le
    _ = _ := by ring

theorem coefficient_nonzero_lower {M : ℕ} (hM : 0 < M) (q : ℚ)
    (hq : coefficient M q ≠ 0) : 1 / (M : ℚ) ≤ |coefficient M q| := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have hk : round ((M : ℚ) * q) ≠ 0 := by
    intro hk
    apply hq
    simp only [coefficient, hk, Int.cast_zero, zero_div]
  have ha : (1 : ℤ) ≤ |round ((M : ℚ) * q)| := by
    have hp := abs_nonneg (round ((M : ℚ) * q))
    have hn := abs_ne_zero.mpr hk
    omega
  have ha' : (1 : ℚ) ≤ |(round ((M : ℚ) * q) : ℚ)| := by exact_mod_cast ha
  rw [coefficient, abs_div, abs_of_pos hm]
  exact div_le_div_of_nonneg_right ha' hm.le

theorem coefficient_upper {M W : ℕ} (hM : 0 < M) (q : ℚ) (hq : |q| ≤ W) :
    |coefficient M q| ≤ W + 1 := by
  have hm : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have he := coefficient_error hM q
  have hhalf : (1 : ℚ) / (2 * M) ≤ 1 := by apply (div_le_one (by positivity)).mpr; linarith
  have h := abs_add_le (coefficient M q - q) q
  rw [sub_add_cancel] at h
  rw [abs_sub_comm] at he
  linarith

end ContinuumCoulomb.SourceCoefficientRounding

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceZeroFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual deletion of zero source bonds after common-denominator rounding. -/

namespace ContinuumCoulomb.SourceZeroFilter
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem nonzero_mem (xs : List Bond) (e : Bond) (he : e ∈ xs.filter keep) : e.2.2 ≠ 0 := by
  exact of_decide_eq_true (List.mem_filter.mp he).2

end ContinuumCoulomb.SourceZeroFilter

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source rounding and zero deletion feed the complete three-stage
spin comparison. Only the source's upper coefficient and gap bounds are
needed; a nonzero lower coefficient bound is proved by rounding. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum
open Matrix MediatorIteration MediatorListProgram SourceBondLists
open scoped BigOperators

theorem family_bounds (d : SquareLatticeHeisenberg) {M W : ℕ} (hM : 0 < M)
    (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    ∀ e, 1 / ((M + W + 1 : ℕ) : ℝ) ≤ |((family d M).weight e : ℝ)| ∧
      |((family d M).weight e : ℝ)| ≤ (M + W + 1 : ℕ) := by
  intro e
  have he := List.get_mem (retained d M) e
  have hz := SourceZeroFilter.nonzero_mem (rounded d M) _ he
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_filter.mp he).1
  have hw : (family d M).weight e = SourceCoefficientRounding.coefficient M (d.coefficient i) := by
    exact congrArg (fun a : _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond => a.2.2) hi.symm
  have hz' : SourceCoefficientRounding.coefficient M (d.coefficient i) ≠ 0 := by simpa only [← hi] using hz
  have hl : 1 / (M : ℝ) ≤ |(SourceCoefficientRounding.coefficient M (d.coefficient i) : ℝ)| := by
    have hq := Rat.cast_le (K := ℝ).mpr
      (SourceCoefficientRounding.coefficient_nonzero_lower hM (d.coefficient i) hz')
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs] using hq
  have hq : |d.coefficient i| ≤ (W : ℚ) := by exact_mod_cast hW i
  have hu : |(SourceCoefficientRounding.coefficient M (d.coefficient i) : ℝ)| ≤ W + 1 := by
    exact_mod_cast SourceCoefficientRounding.coefficient_upper hM (d.coefficient i) hq
  rw [hw]
  constructor
  · exact (one_div_le_one_div_of_le (by exact_mod_cast hM)
      (by norm_cast; omega : (M : ℝ) ≤ (M + W + 1 : ℕ))).trans hl
  · have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    push_cast
    linarith

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial common denominator absorbs both coefficient rounding
and all three mediator errors into one inverse-polynomial promise budget. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum

theorem denominator_pos (r : ℕ) {G : ℕ} (hG : 0 < G) : 0 < denominator r G := by
  unfold denominator
  positivity

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizationCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The machine-normalized source registers are the literal bond family
whose complete positive-spin spectral and promise estimates were proved. -/

namespace ContinuumCoulomb.SourceMetadataProgram
open MediatorListProgram

theorem size_pos (d : BinaryHeisenberg) : 0 < size d := by
  unfold size
  omega

theorem polynomialPromise_weight (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) :
    ∀ e, |((d.toSource h).coefficient e : ℝ)| ≤ (size d ^ k : ℕ) := by
  intro e
  simpa only [size, Nat.cast_pow, Nat.cast_add, Nat.cast_one, BinaryHeisenberg.toSource] using
    hp.weight_bound e

end ContinuumCoulomb.SourceMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourceContactProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal composition from the encoded source to the calibrated
contact coordinates. The signed retained bonds determine the geometric
strips; the final positive bond list supplies their nineteen target weights. -/

namespace ContinuumCoulomb.SourceContactProgram
open ExactQuantumFactoring.BitStackProgram

theorem size_ge_two (d : BinaryHeisenberg) : 2 ≤ size d := by
  simp only [size,SourceMetadataProgram.size]
  omega

end ContinuumCoulomb.SourceContactProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialUnaryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the runtime bound of an actual unary-output procedure into a
single fixed power of the source input length, as needed by calibration. -/

namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

theorem natPolynomial_power_bound (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, p.eval n ≤ (n + 2) ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b + 1, fun n => ?_⟩
    have hbase : 1 ≤ n + 2 := by omega
    have hpa : (n + 2) ^ a ≤ (n + 2) ^ (a + b) :=
      pow_le_pow_right₀ hbase (by omega)
    have hpb : (n + 2) ^ b ≤ (n + 2) ^ (a + b) :=
      pow_le_pow_right₀ hbase (by omega)
    rw [Polynomial.eval_add, pow_succ]
    calc
      p.eval n + q.eval n ≤ (n + 2) ^ (a + b) + (n + 2) ^ (a + b) :=
        Nat.add_le_add ((ha n).trans hpa) ((hb n).trans hpb)
      _ = (n + 2) ^ (a + b) * 2 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  | monomial i c =>
    refine ⟨c + i, fun n => ?_⟩
    have hc : c ≤ (n + 2) ^ c :=
      (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left (by omega) c)
    rw [Polynomial.eval_monomial, pow_add]
    exact Nat.mul_le_mul hc (Nat.pow_le_pow_left (by omega) i)

theorem unaryProcedure_power_bound {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) :
    ∃ k : ℕ, ∀ a, f a ≤ ((ea a).length + 2) ^ k := by
  obtain ⟨k, hk⟩ := natPolynomial_power_bound (Polynomial.X + p.bound)
  refine ⟨k, fun a => ?_⟩
  have h := p.output_length_le a
  simp only [unaryCode, List.length_replicate] at h
  exact h.trans (by simpa only [Polynomial.eval_add, Polynomial.eval_X] using hk (ea a).length)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceEncodingSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size bounds for the actual binary source serialization. In particular,
the number of sites and edges is bounded by the input bit length. -/

namespace ContinuumCoulomb
open BinaryEncoding

namespace BinaryEncoding

theorem natural_length_pos (n : ℕ) : 0 < (natural.encode n).length := by
  rw [natural_length]
  omega

theorem integer_length_pos (z : ℤ) : 0 < (integer.encode z).length := by
  cases z <;> simp only [integer, List.length_cons] <;> omega

theorem list_count_le {α : Type*} (a : Codec α) (ha : ∀ x, 0 < (a.encode x).length)
    (xs : List α) : xs.length ≤ ((list a).encode xs).length := by
  have hsum : xs.length ≤ (xs.map (fun x => (a.encode x).length)).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hx := ha x
      omega
  rw [list_length]
  omega

end BinaryEncoding

theorem binaryHeisenbergEdge_length_pos (e : BinaryHeisenbergEdge) :
    0 < (binaryHeisenbergEdgeCodec.encode e).length := by
  change 0 < (natural.encode e.left ++
    (natural.encode e.right ++ binaryRationalCodec.encode e.coefficient)).length
  simp only [List.length_append]
  have h := natural_length_pos e.left
  omega

theorem binaryHeisenberg_count_le_length (d : BinaryHeisenberg) :
    d.coordinate.length + d.edges.length ≤ (binaryHeisenbergCodec.encode d).length := by
  have hc := list_count_le (pair integer integer)
    (fun p => by rw [pair_length]; have h := integer_length_pos p.1; omega) d.coordinate
  have he := list_count_le binaryHeisenbergEdgeCodec binaryHeisenbergEdge_length_pos d.edges
  change d.coordinate.length + d.edges.length ≤
    ((BinaryEncoding.list (pair integer integer)).encode d.coordinate ++
      ((BinaryEncoding.list binaryHeisenbergEdgeCodec).encode d.edges ++
        (binaryRationalCodec.encode d.lower ++ binaryRationalCodec.encode d.upper))).length
  simp only [List.length_append]
  omega

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePositiveBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source normalization and metadata programs give one fixed
polynomial coefficient exponent for the final positive-spin graph. -/

noncomputable section
namespace ContinuumCoulomb.SourceMetadataProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

attribute [local irreducible] MediatorParameters.finalWeight

theorem finalBound_power (k : ℕ) :
    ∃ A : ℕ, ∀ d, finalBound k d ≤ ((binaryHeisenbergCodec.encode d).length + 2) ^ A :=
  unaryProcedure_power_bound (finalBoundProgram k)

private theorem envWeight_congr (x : Env) (r W G n : ℕ) (h : x = (r, W, G, n)) :
    MediatorParameters.finalWeight x.1 x.2.1 x.2.2.1 =
      MediatorParameters.finalWeight r W G := by
  cases h
  rfl

private theorem finalBound_of_env (k : ℕ) (d : BinaryHeisenberg) (r W G n : ℕ)
    (he : (SourceNormalizationProgram.normalized (input k d)).1 = (r, W, G, n)) :
    finalBound k d = MediatorParameters.finalWeight r W G := by
  exact envWeight_congr ((SourceNormalizationProgram.normalized (input k d)).1) r W G n he

theorem finalBound_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    finalBound k d = MediatorParameters.finalWeight
      (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length
      (roundingDenominator k d + size d ^ k + 1) (size d ^ k) := by
  have he : (SourceNormalizationProgram.normalized (input k d)).1 =
      ((SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length,
        roundingDenominator k d + size d ^ k + 1, size d ^ k, d.coordinate.length) :=
    congrArg Prod.fst (normalized_eq k d h)
  exact finalBound_of_env k d
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length
    (roundingDenominator k d + size d ^ k + 1) (size d ^ k) d.coordinate.length he

theorem retained_count_le (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      d.edges.length := by
  have hf := List.length_filter_le SourceZeroFilter.keep
    (SourceNormalizedSpectrum.rounded (d.toSource h) (roundingDenominator k d))
  simpa only [SourceNormalizedSpectrum.retained, SourceNormalizedSpectrum.rounded,
    List.length_ofFn, BinaryHeisenberg.toSource] using hf

theorem positive_graph_count_bound (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    d.coordinate.length + 18 *
        (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      19 * (binaryHeisenbergCodec.encode d).length ∧
    19 * (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      19 * (binaryHeisenbergCodec.encode d).length := by
  have hr := retained_count_le k d h
  have hc := binaryHeisenberg_count_le_length d
  constructor <;> omega

/-- One fixed exponent controls every final coefficient, even when the
original source contains zero or exponentially tiny rational coefficients. -/
theorem source_positive_weight_range (k : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (d : BinaryHeisenberg) (h : d.Valid),
      d.PolynomialPromise k → ∀ e,
      (((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A)⁻¹ ≤
        ((MediatorIteration.finalGraph
          (SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d))
          (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ∧
      ((MediatorIteration.finalGraph
          (SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d))
          (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ≤
        ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A := by
  obtain ⟨A, hA⟩ := finalBound_power k
  refine ⟨A + 1, by omega, fun d h hp e => ?_⟩
  have hG : 0 < size d ^ k := pow_pos (size_pos d) k
  have hM : 0 < roundingDenominator k d :=
    SourceNormalizedSpectrum.denominator_pos d.edges.length hG
  have hW : 0 < roundingDenominator k d + size d ^ k + 1 := by omega
  have hB := SourceNormalizedSpectrum.family_bounds (d.toSource h) hM
    (polynomialPromise_weight k d h hp)
  have hlo := MediatorIteration.finalGraph_lower _ hW hG (fun i => (hB i).2) (fun i => (hB i).1) e
  have hhi := MediatorIteration.finalGraph_upper _ hW hG (fun i => (hB i).2) (fun i => (hB i).1) e
  have hsize : 2 ≤ (binaryHeisenbergCodec.encode d).length + 2 := by omega
  have hpow : (2 : ℝ) ≤ ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ (A + 1) := by
    exact_mod_cast hsize.trans (Nat.le_self_pow (by omega : A + 1 ≠ 0) _)
  constructor
  · have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow
    norm_num only [one_div] at hi
    exact hi.trans hlo
  · apply hhi.trans
    rw [← finalBound_eq k d h]
    have hn := (hA d).trans (Nat.pow_le_pow_right (by omega : 1 ≤
      (binaryHeisenbergCodec.encode d).length + 2) (by omega : A ≤ A + 1))
    exact_mod_cast hn

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGeometryBounds
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial site counts, coordinate extent and coefficient ranges for
the literal normalized source passed to the contact realization. -/

noncomputable section
namespace ContinuumCoulomb.SourceMetadataProgram
open ContactMediator

private theorem nineteen_mul_le_sixth (L : ℕ) : 19 * L ≤ (L + 2) ^ 6 := by
  have h19 : 19 ≤ (L + 2) ^ 5 :=
    (by norm_num : 19 ≤ 2 ^ 5).trans (Nat.pow_le_pow_left (by omega) 5)
  calc
    19 * L ≤ (L + 2) ^ 5 * (L + 2) := Nat.mul_le_mul h19 (by omega)
    _ = (L + 2) ^ 6 := by ring

theorem geometricSource_count (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (Fintype.card (GlobalSite (geometricSource k d h)) : ℝ) ≤
      ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ 6 := by
  have hc := (positive_graph_count_bound k d h).1
  have hp := hc.trans (nineteen_mul_le_sixth (binaryHeisenbergCodec.encode d).length)
  rw [globalSite_card]
  change ((d.coordinate.length + 18 *
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length : ℕ) : ℝ) ≤ _
  exact_mod_cast hp

theorem geometricSource_weight_range (k : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (d : BinaryHeisenberg) (h : d.Valid), d.PolynomialPromise k →
      ∀ e : GlobalEdge (geometricSource k d h),
        (((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A)⁻¹ ≤
          ((MediatorIteration.finalGraph (geometricSource k d h).bonds
            (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ∧
        ((MediatorIteration.finalGraph (geometricSource k d h).bonds
            (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ≤
          ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A := by
  obtain ⟨A, hA, hweight⟩ := source_positive_weight_range k
  exact ⟨A, hA, hweight⟩

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PrefactorSourceContactCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prefactor-aware program retains the exact final graph enumeration,
and calibrates its original weights at the physical unit-charge scale. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ContactMediator

theorem electron_count (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (SourcePositiveProgram.output s d).vertices =
      Fintype.card (GlobalSite (SourceMetadataProgram.geometricSource s d hd)) := by
  rw [SourcePositiveProgram.vertices_eq s d hd]
  simp only [GlobalSite,Fintype.card_fin]
  rfl

theorem source_weight_range (s : ℕ) : ∃ A : ℕ, 0 < A ∧
    ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
    ∀ e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd),
      ((CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A)⁻¹ ≤
        SourceContactProgram.weights s d hd e ∧
      (SourceContactProgram.weights s d hd e:ℝ) ≤
        (CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A := by
  obtain ⟨A,hA,hweight⟩ := SourceMetadataProgram.geometricSource_weight_range s
  refine ⟨A,hA,fun d hd hp e => ?_⟩
  obtain ⟨hlo,hhi⟩ := hweight d hd hp e
  have hn : (1:ℝ) ≤ SourceContactProgram.size d := by
    exact_mod_cast (show 1 ≤ SourceContactProgram.size d from
      le_trans (by decide : 1 ≤ 2) (SourceContactProgram.size_ge_two d))
  have hbase : (SourceContactProgram.size d:ℝ) ≤
      CalibrationMesh.base (SourceContactProgram.size d) := by
    simp only [CalibrationMesh.base,Nat.cast_pow]
    exact le_self_pow₀ hn (by decide)
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ SourceContactProgram.size d) hbase A
  have hsize : (SourceContactProgram.size d:ℝ) =
      (binaryHeisenbergCodec.encode d).length + 2 := by
    simp only [SourceContactProgram.size,SourceMetadataProgram.size,Nat.cast_add,Nat.cast_one]
    ring
  have hlo' : ((SourceContactProgram.size d:ℝ)^A)⁻¹ ≤
      (SourceContactProgram.weights s d hd e:ℝ) := by
    simpa only [hsize,SourceContactProgram.weights,SourcePositiveProgram.sourceBound] using hlo
  have hhi' : (SourceContactProgram.weights s d hd e:ℝ) ≤
      (SourceContactProgram.size d:ℝ)^A := by
    simpa only [hsize,SourceContactProgram.weights,SourcePositiveProgram.sourceBound] using hhi
  refine ⟨?_,hhi'.trans hpow⟩
  have hpos : (0:ℝ) < (SourceContactProgram.size d:ℝ)^A := by positivity
  have hinv : ((CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A)⁻¹ ≤
      ((SourceContactProgram.size d:ℝ)^A)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hpos hpow
  exact hinv.trans hlo'

end ContinuumCoulomb.PrefactorSourceContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialHoppingSmallness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit natural exponents make calibrated hopping perturbatively
small and leave an inverse-polynomial fraction of its squared scale. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem pow_mul_inverse_add {N : ℝ} (hN : 0 < N) (a b : ℕ) :
    N ^ a * (N ^ (a + b))⁻¹ = (N ^ b)⁻¹ := by
  rw [pow_add, mul_inv_rev]
  field_simp [pow_ne_zero a hN.ne', pow_ne_zero b hN.ne']

theorem inverse_power_lt_half {N : ℝ} (hN : 2 ≤ N) {E : ℕ} (hE : 2 ≤ E) :
    (N ^ E)⁻¹ < 1 / 2 := by
  have hNp : 0 < N := by linarith
  have hp : (4 : ℝ) ≤ N ^ E := by
    have hs : (4 : ℝ) ≤ N ^ 2 := by nlinarith
    exact hs.trans (pow_le_pow_right₀ (by linarith : 1 ≤ N) hE)
  have hi : (N ^ E)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  exact hi.trans_lt (by norm_num)

theorem polynomial_hubbard_error_budget {N c : ℝ} (hN : 0 < N) (R A L g : ℕ)
    (hc : 2 * c ≤ N ^ L) :
    let C := R + A + 2 * L + 2
    let E := g + 2 * C + L
    let B := E + C
    2 * c * ((N ^ E)⁻¹) ^ 3 ≤ (N ^ g)⁻¹ * ((N ^ B)⁻¹) ^ 2 := by
  intro C E B
  calc
    _ ≤ N ^ L * ((N ^ E)⁻¹) ^ 3 :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (inv_nonneg.mpr (pow_nonneg hN.le E)) 3)
    _ = N ^ L * (N ^ (E * 3))⁻¹ := by rw [inv_pow (N ^ E) 3, ← pow_mul]
    _ = (N ^ (g + B * 2))⁻¹ := by
      rw [show E * 3 = L + (g + B * 2) by dsimp [B, E, C]; omega, pow_mul_inverse_add hN]
    _ = _ := by rw [pow_add, pow_mul, mul_inv_rev, inv_pow]; ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceFinalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact final graph indexed by the literal output vertex count.
Changing only the proof of that count preserves every bond and weight. -/

noncomputable section
namespace ContinuumCoulomb.MediatorIteration

theorem Bonds.castSites_noLoops {n n' r : ℕ} (h : n=n') (F : Bonds n r) (hF : F.NoLoops) :
    (F.castSites h).NoLoops := by cases h; exact hF

theorem Bonds.castSites_simple {n n' r : ℕ} (h : n=n') (F : Bonds n r) (hF : F.Simple) :
    (F.castSites h).Simple := by cases h; exact hF

end ContinuumCoulomb.MediatorIteration

namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration SourceMetadataProgram ContactMediator

theorem graph_weight (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).weight=SourceContactProgram.weights s d hd := by
  unfold graph
  erw [Bonds.castSites_weight]
  rfl

theorem graph_noLoops (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).NoLoops :=
  Bonds.castSites_noLoops _ _ (finalGraph_noLoops _ _ _)

theorem graph_simple (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).Simple :=
  Bonds.castSites_simple _ _ (finalGraph_simple _ _ _)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_TargetHubbardParameters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Hubbard approximation uses exact Coulomb target amplitudes;
the negative sign agrees with the manufactured well matrix. Its spatial
implementation can then be approximated entrywise. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem target_hopping_sum_bound {Edge : Type*} [Fintype Edge]
    (freq τ B : ℝ) (hτ : 0 ≤ τ) (distance K : Edge → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hB : ∀ e, K e ≤ B) :
    4 * ∑ e, |coulombHoppingTarget freq τ (K e) (distance e)| ≤
      4 * (Fintype.card Edge : ℝ) * (τ * Real.sqrt (B * localizedCoulombProfile freq 0)) := by
  have hpoint (e : Edge) : |coulombHoppingTarget freq τ (K e) (distance e)| ≤
      τ * Real.sqrt (B * localizedCoulombProfile freq 0) := by
    rw [coulombHoppingTarget, abs_of_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))]
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hτ
    calc
      _ ≤ K e * localizedCoulombProfile freq 0 := mul_le_mul_of_nonneg_left
        (sub_le_self _ (localizedCoulombProfile_nonnegative freq (distance e))) (hK e)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hB e) (localizedCoulombProfile_nonnegative freq 0)
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)) (by norm_num : (0 : ℝ) ≤ 4)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h

theorem polynomial_target_hopping_smallness {Edge : Type*} [Fintype Edge]
    {freq N : ℝ} (hN : 2 ≤ N) (R A L E : ℕ)
    (hc : (N ^ L)⁻¹ ≤ localizedGramConstant freq)
    (hU : Real.sqrt (localizedCoulombProfile freq 0) ≤ N ^ L)
    (hr : (Fintype.card Edge : ℝ) ≤ N ^ R) (distance K : Edge → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hKhi : ∀ e, K e ≤ N ^ A) :
    4 * ∑ e, |coulombHoppingTarget freq (N ^ (E + (R + A + 2 * L + 2)))⁻¹ (K e) (distance e)| ≤ (N ^ E)⁻¹ * localizedGramConstant freq := by
  have hNp : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  let B := E + (R + A + 2 * L + 2)
  have hτ : 0 ≤ (N ^ B)⁻¹ := inv_nonneg.mpr (pow_nonneg hNp.le B)
  have hsqrt : Real.sqrt (N ^ A * localizedCoulombProfile freq 0) ≤ N ^ (A + L) := by
    rw [Real.sqrt_mul (pow_nonneg hNp.le A), pow_add]
    apply mul_le_mul ?_ hU (Real.sqrt_nonneg _) (pow_nonneg hNp.le A)
    apply Real.sqrt_le_iff.mpr
    have hp : 1 ≤ N ^ A := one_le_pow₀ hN₁
    exact ⟨by positivity, by nlinarith only [hp]⟩
  have hb := target_hopping_sum_bound freq (N ^ B)⁻¹ (N ^ A) hτ distance K hK hKhi
  have hbound : 4 * (Fintype.card Edge : ℝ) * ((N ^ B)⁻¹ *
      Real.sqrt (N ^ A * localizedCoulombProfile freq 0)) ≤ 4 * (N ^ (E + L + 2))⁻¹ := by
    calc
      _ ≤ 4 * N ^ R * ((N ^ B)⁻¹ * N ^ (A + L)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num))
          (mul_le_mul_of_nonneg_left hsqrt hτ)
          (mul_nonneg hτ (Real.sqrt_nonneg _)) (by positivity)
      _ = 4 * (N ^ (R + (A + L)) * (N ^ B)⁻¹) := by rw [pow_add]; ring
      _ = _ := by
        rw [show B = (R + (A + L)) + (E + L + 2) by dsimp [B]; omega,
          pow_mul_inverse_add hNp]
  have hfour : 4 * (N ^ (E + L + 2))⁻¹ ≤ (N ^ (E + L))⁻¹ := by
    have hsq : (4 : ℝ) ≤ N ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq (pow_nonneg hNp.le (E + L))
    have hratio : 4 / N ^ (E + L + 2) ≤ 1 / N ^ (E + L) :=
      (div_le_div_iff₀ (pow_pos hNp (E + L + 2)) (pow_pos hNp (E + L))).mpr
        (by simpa only [pow_add, one_mul, mul_one, mul_comm] using h)
    simpa only [div_eq_mul_inv, one_mul] using hratio
  have hlast : (N ^ (E + L))⁻¹ ≤ (N ^ E)⁻¹ * localizedGramConstant freq := by
    have h := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (pow_nonneg hNp.le E))
    simpa only [pow_add, mul_inv_rev, mul_comm] using h
  exact hb.trans (hbound.trans (hfour.trans hlast))

theorem exists_uniform_target_hubbard_parameters {freq : ℝ} (hfreq : 0 < freq) (R A g : ℕ) :
    ∃ E B : ℕ, 2 ≤ E ∧ 0 < B ∧ ∀ N : ℝ, 2 ≤ N → ∀ (r : ℕ), (r:ℝ) ≤ N^R →
      ∀ D : ℝ, 5 ≤ D → ∀ (m : ℕ) (u : Fin (m+1) → PlanarPosition),
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (m+1:ℕ)*localLeakageBound freq D ≤ localDualMass freq/2 →
      ∀ (left right : Fin r → Fin (m+1)) (K : Fin r → ℝ),
      (∀ e, 0 ≤ K e) → (∀ e, K e ≤ N^A) →
      (∀ e, left e ≠ right e) →
      (∀ e f, e ≠ f → ¬(left e=left f ∧ right e=right f) ∧ ¬(left e=right f ∧ right e=left f)) →
      |HubbardGlobal.hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right (fun e => -coulombHoppingTarget freq (N^B)⁻¹ (K e) ‖u (left e)-u (right e)‖)-
        HubbardGlobal.graphSourceBottom m left right (fun e => ((N^B)⁻¹)^2*K e)| ≤
          (N^g)⁻¹*((N^B)⁻¹)^2 := by
  obtain ⟨L,_,hconstants⟩ := exists_polynomial_constant_bounds (localizedGramConstant_positive hfreq)
    (max (2*localizedGramConstant freq) (Real.sqrt (localizedCoulombProfile freq 0)))
  let C := R+A+2*L+2
  let E := g+2*C+L
  let B := E+C
  have hE : 2 ≤ E := by dsimp [E,C]; omega
  refine ⟨E,B,hE,by dsimp [B,E,C]; omega,?_⟩
  intro N hN r hr D hD m u hsep hleak left right K hK hKhi hloop hsimple
  have hNp : 0 < N := by linarith
  obtain ⟨hc,hupper⟩ := hconstants N hN
  have hc₂ : 2*localizedGramConstant freq ≤ N^L := (le_max_left _ _).trans hupper
  have hU : Real.sqrt (localizedCoulombProfile freq 0) ≤ N^L := (le_max_right _ _).trans hupper
  have ht := polynomial_target_hopping_smallness hN R A L E hc hU (by simpa using hr)
    (fun e => ‖u (left e)-u (right e)‖) K hK hKhi
  have hcal (e : Fin r) :
      (-coulombHoppingTarget freq (N^B)⁻¹ (K e) ‖u (left e)-u (right e)‖)^2 =
      (((N^B)⁻¹)^2*K e)*(localizedCoulombProfile freq 0-localizedCoulombCoeff freq (u (left e)) (u (right e))) := by
    have hg := chargeTransfer_Gram_denominator (localizedCoulombProfile freq 0)
      (localizedGramConstant freq) (localizedOffsiteCoulomb freq u)
      (localizedCoulomb_charge_condition hfreq hD u hsep hleak) (left e) (right e) (hloop e)
      (localizedOffsiteCoulomb_symmetric hfreq u) (localizedOffsiteCoulomb_diagonal freq u)
    simp only [localizedOffsiteCoulomb,ite_eq_right (hloop e)] at hg
    have hn := (localizedGramConstant_positive hfreq).le.trans hg
    rw [localizedCoulombCoeff_distance] at hn ⊢
    rw [neg_sq,coulombHoppingTarget,mul_pow,Real.sq_sqrt (mul_nonneg (hK e) hn)]
    ring
  have he := HubbardGlobal.localized_hubbard_Heisenberg hfreq hD m u hsep hleak left right
    (fun e => -coulombHoppingTarget freq (N^B)⁻¹ (K e) ‖u (left e)-u (right e)‖)
    (fun e => ((N^B)⁻¹)^2*K e) hloop hsimple hcal (by positivity : 0 ≤ (N^E)⁻¹)
    (inverse_power_lt_half hN hE) (by simpa only [abs_neg] using ht)
  exact he.trans (polynomial_hubbard_error_budget hNp R A L g hc₂)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceFiniteBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-Hamiltonian bounds used before selecting the source
geometry and numerical precision. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem exists_target_hopping_exponent (freq : ℝ) (R A : ℕ) :
    ∃ v : ℕ, 1 ≤ v ∧ ∀ (N τ : ℝ), 2 ≤ N → 0 ≤ τ → τ ≤ 1 →
      ∀ {Edge : Type*} [Fintype Edge], (Fintype.card Edge : ℝ) ≤ N^R →
      ∀ (distance K : Edge → ℝ), (∀ e, 0 ≤ K e) → (∀ e, K e ≤ N^A) →
      (∑ e, |coulombHoppingTarget freq τ (K e) (distance e)|) ≤ N^v := by
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1)
    (Real.sqrt (localizedCoulombProfile freq 0))
  refine ⟨R+A+q,by omega,?_⟩
  intro N τ hN hτ hτ1 Edge _ hcard distance K hK hKhi
  have hN1 : 1 ≤ N := by linarith
  have hsqrt : Real.sqrt (N^A*localizedCoulombProfile freq 0) ≤ N^(A+q) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ N^A),pow_add]
    apply mul_le_mul ?_ (hconst N hN).2 (Real.sqrt_nonneg _) (by positivity)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [one_le_pow₀ hN1 (n := A)]
  have hτsqrt : τ*Real.sqrt (N^A*localizedCoulombProfile freq 0) ≤ N^(A+q) :=
    (mul_le_mul_of_nonneg_right hτ1 (Real.sqrt_nonneg _)).trans (by simpa using hsqrt)
  have hcardmul := mul_le_mul hcard hτsqrt
    (mul_nonneg hτ (Real.sqrt_nonneg _)) (by positivity : (0:ℝ) ≤ N^R)
  rw [← pow_add] at hcardmul
  have ht := target_hopping_sum_bound freq τ (N^A) hτ distance K hK hKhi
  have h4 := mul_le_mul_of_nonneg_left hcardmul (by norm_num : (0:ℝ) ≤ 4)
  have he : R+(A+q)=R+A+q := by omega
  rw [he] at h4
  nlinarith only [ht,h4]

theorem localLeakageBound_antitone (freq : ℝ) {a b : ℝ} (hab : a ≤ b) :
    localLeakageBound freq b ≤ localLeakageBound freq a := by
  unfold localLeakageBound
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq))
    (MeasureTheory.integral_nonneg (fun _ => abs_nonneg _))

theorem exists_source_leakage_threshold {freq : ℝ} (hfreq : 0 < freq) (R : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ (k : ℕ), q ≤ k → ∀ (N D : ℝ), 2 ≤ N →
      25*(k:ℝ)*Real.log N ≤ D → ∀ M : ℕ, (M:ℝ) ≤ N^R →
      5 ≤ D ∧ (M:ℝ)*localLeakageBound freq D ≤ localDualMass freq/2 := by
  obtain ⟨q,hq,hspacing⟩ := exists_localizedGram_spacing hfreq R
  refine ⟨q,by omega,fun k hk N D hN hD M hM => ?_⟩
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hqk : (q:ℝ) ≤ 25*(k:ℝ) := by
    have hh : (q:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Nat.cast_nonneg k (α := ℝ)]
  have hqd : (q:ℝ)*Real.log N ≤ D := (mul_le_mul_of_nonneg_right hqk hlog).trans hD
  obtain ⟨hfive,hleak⟩ := hspacing N hN
  refine ⟨hfive.trans hqd,?_⟩
  exact (mul_le_mul hM (localLeakageBound_antitone freq hqd)
    (localLeakageBound_nonnegative freq D) (by positivity)).trans hleak

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGraphIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual contact-site enumeration and the finite Hubbard graph use
one common electron index. Relabeling changes no bond or coordinate order. -/

noncomputable section
namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration ContactMediator SourceMetadataProgram

theorem indexedGraph_weight (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) :
    (indexedGraph s d hd hm).weight=SourceContactProgram.weights s d hd := by
  rw [indexedGraph,Bonds.castSites_weight,graph_weight]

theorem indexedGraph_noLoops (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) : (indexedGraph s d hd hm).NoLoops := by
  unfold indexedGraph
  exact Bonds.castSites_noLoops hm _ (graph_noLoops s d hd)

theorem indexedGraph_simple (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) : (indexedGraph s d hd hm).Simple := by
  unfold indexedGraph
  exact Bonds.castSites_simple hm _ (graph_simple s d hd)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceTargetHubbard
attribute [-simp] _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal positive source graph satisfies the finite Hubbard
approximation with uniform exponents fixed before its coordinates are chosen. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open SourcePositiveProgram SourceMetadataProgram ContactMediator HubbardGlobal

private theorem source_size_cast (d : BinaryHeisenberg) :
    (SourceContactProgram.size d:ℝ)=(binaryHeisenbergCodec.encode d).length+2 := by
  unfold SourceContactProgram.size SourceMetadataProgram.size
  push_cast
  ring

theorem source_graph_site_count (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    ((output s d).vertices:ℝ) ≤ (SourceContactProgram.size d:ℝ)^6 := by
  rw [PrefactorSourceContactProgram.electron_count s d hd,source_size_cast]
  exact geometricSource_count s d hd

theorem source_graph_edge_count (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graphEdgeCount s d hd:ℝ) ≤ (SourceContactProgram.size d:ℝ)^7 := by
  have hN : (2:ℝ) ≤ SourceContactProgram.size d := by
    exact_mod_cast SourceContactProgram.size_ge_two d
  have hnat : graphEdgeCount s d hd ≤ 2*(output s d).vertices := by
    rw [PrefactorSourceContactProgram.electron_count s d hd,globalSite_card]
    unfold graphEdgeCount
    omega
  have hr : (graphEdgeCount s d hd:ℝ) ≤ 2*((output s d).vertices:ℝ) := by exact_mod_cast hnat
  calc
    _ ≤ 2*(SourceContactProgram.size d:ℝ)^6 :=
      hr.trans (mul_le_mul_of_nonneg_left (source_graph_site_count s d hd) (by norm_num))
    _ ≤ (SourceContactProgram.size d:ℝ)^7 := by
      calc
        _ ≤ (SourceContactProgram.size d:ℝ)*(SourceContactProgram.size d:ℝ)^6 :=
          mul_le_mul_of_nonneg_right hN (by positivity)
        _ = _ := by rw [pow_succ]; ring

theorem exists_source_hopping_exponent (freq : ℝ) (A : ℕ) :
    ∃ v : ℕ, 1 ≤ v ∧ ∀ (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
      (m : ℕ) (hm : (output s d).vertices=m+1) (B : ℕ),
      let F := indexedGraph s d hd hm
      let N : ℝ := SourceContactProgram.size d
      (∀ e, (N^(30*A))⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ N^(30*A)) →
      ∀ u : Fin (m+1) → PlanarPosition,
      (∑ e, |-coulombHoppingTarget freq (N^(30*B))⁻¹ (F.weight e)
        ‖u (F.left e)-u (F.right e)‖|) ≤ N^v := by
  obtain ⟨v,hv,hbound⟩ := exists_target_hopping_exponent freq 7 (30*A)
  refine ⟨v,hv,fun s d hd m hm B => ?_⟩
  dsimp only
  intro hweights u
  let N : ℝ := SourceContactProgram.size d
  let F := indexedGraph s d hd hm
  have hN : (2:ℝ) ≤ N := by
    change (2:ℝ) ≤ (SourceContactProgram.size d:ℝ)
    exact_mod_cast SourceContactProgram.size_ge_two d
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hK (e : Fin (graphEdgeCount s d hd)) : 0 ≤ (F.weight e:ℝ) :=
    (inv_nonneg.mpr (pow_nonneg hN0.le _)).trans (hweights e).1
  have hcard : (Fintype.card (Fin (graphEdgeCount s d hd)):ℝ) ≤ N^7 := by
    simpa only [Fintype.card_fin] using source_graph_edge_count s d hd
  have hs := hbound N (N^(30*B))⁻¹ hN
    (inv_nonneg.mpr (pow_nonneg hN0.le _))
    (inv_le_one_of_one_le₀ (one_le_pow₀ hN1))
    (Edge := Fin (graphEdgeCount s d hd)) hcard
    (fun e => ‖u (F.left e)-u (F.right e)‖) (fun e => (F.weight e:ℝ)) hK
    (fun e => (hweights e).2)
  apply le_trans _ hs
  apply Finset.sum_le_sum
  intro e _
  exact (abs_neg _).le

theorem exists_source_target_parameters_oai (rho : ℕ) (hrho : 0 < rho) (s g : ℕ) :
    ∃ A B v q : ℕ, 0 < A ∧ 0 < B ∧ 1 ≤ v ∧ 1 ≤ q ∧
      ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
      ∀ (m k : ℕ) (hm : (output s d).vertices=m+1), q ≤ k →
      ∀ (D : ℝ) (u : Fin (m+1) → PlanarPosition),
      25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ D →
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      let F := indexedGraph s d hd hm
      let N : ℝ := SourceContactProgram.size d
      let τ := (N^(30*B))⁻¹
      let freq := GaussianFrequency.frequency rho
      let t := fun e => -coulombHoppingTarget freq τ (F.weight e) ‖u (F.left e)-u (F.right e)‖
      (∀ e, (N^(30*A))⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ N^(30*A)) ∧
      (∑ e, |t e|) ≤ N^v ∧
      |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
          F.left F.right t-
        graphSourceBottom m F.left F.right (fun e => τ^2*(F.weight e:ℝ))| ≤ (N^g)⁻¹*τ^2 := by
  have hf := manufactured_frequency_positive hrho
  obtain ⟨A,hA,hweights⟩ := PrefactorSourceContactProgram.source_weight_range s
  obtain ⟨E,B,_hE,hB,hfinite⟩ := exists_uniform_target_hubbard_parameters hf 7 A g
  obtain ⟨v,hv,hvbound⟩ := exists_source_hopping_exponent (GaussianFrequency.frequency rho) A
  obtain ⟨q,hq,hqbound⟩ := exists_source_leakage_threshold hf 6
  refine ⟨A,B,v,q,hA,hB,hv,hq,?_⟩
  intro d hd hp m k hm hk D u hD hsep
  dsimp only
  let F := indexedGraph s d hd hm
  let N : ℝ := SourceContactProgram.size d
  let M : ℝ := CalibrationMesh.base (SourceContactProgram.size d)
  have hN : 2 ≤ N := by
    change (2:ℝ) ≤ (SourceContactProgram.size d:ℝ)
    exact_mod_cast SourceContactProgram.size_ge_two d
  have hM : 2 ≤ M := by
    change (2:ℝ) ≤ (CalibrationMesh.base (SourceContactProgram.size d):ℝ)
    exact_mod_cast CalibrationMesh.base_ge_two (SourceContactProgram.size_ge_two d)
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num : (1:ℝ) ≤ 2) hN
  have hNM : N ≤ M := by
    dsimp [M,CalibrationMesh.base,N]
    rw [Nat.cast_pow]
    exact le_self_pow₀ hN1 (by decide)
  have hMpow (a : ℕ) : M^a=N^(30*a) := by
    dsimp only [M,CalibrationMesh.base,N]
    rw [Nat.cast_pow,← pow_mul]
  have hFweight : F.weight=SourceContactProgram.weights s d hd := indexedGraph_weight s d hd hm
  have hKr (e : Fin (graphEdgeCount s d hd)) : (M^A)⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ M^A := by
    rw [hFweight]
    exact hweights d hd hp e
  have hK (e : Fin (graphEdgeCount s d hd)) : 0 ≤ (F.weight e:ℝ) :=
    (inv_nonneg.mpr (pow_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 2) hM) A)).trans (hKr e).1
  have hcount : (m+1:ℕ) ≤ N^6 := by
    rw [← hm]
    exact source_graph_site_count s d hd
  obtain ⟨hfive,hleak⟩ := hqbound k hk N D hN hD (m+1) hcount
  have heN : (graphEdgeCount s d hd:ℝ) ≤ N^7 := source_graph_edge_count s d hd
  have heM : (graphEdgeCount s d hd:ℝ) ≤ M^7 :=
    heN.trans (pow_le_pow_left₀ hN0.le hNM 7)
  have hloop := indexedGraph_noLoops s d hd hm
  have hsimple := (indexedGraph_simple s d hd hm).hypothesis
  have herr := hfinite M hM _ heM D hfive m u hsep hleak F.left F.right
    (fun e => (F.weight e:ℝ)) hK (fun e => (hKr e).2) hloop hsimple
  have hKpower (e : Fin (graphEdgeCount s d hd)) :
      (N^(30*A))⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ N^(30*A) := by
    simpa only [hMpow] using hKr e
  refine ⟨hKpower,hvbound s d hd m hm B hKpower u,?_⟩
  rw [hMpow B] at herr
  exact herr.trans (mul_le_mul_of_nonneg_right
      (inv_anti₀ (pow_pos hN0 g) (pow_le_pow_left₀ hN0.le hNM g)) (sq_nonneg _))

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.exists_source_target_parameters_oai := @OAI.ContinuumCoulomb.exists_source_target_parameters_oai
