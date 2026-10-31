-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:20:58.83964+00:00
-- url     : https://prove2.me/submissions/f6c2f222-8b10-4864-ac98-43b208312bf4

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Native_command_value
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_scalar_value_eq_target

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LiftRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFinite _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The finite free ring used for prime-power counting

This file constructs the quotient by a monic polynomial, proves that a
positive-degree quotient retains the base ring, and constructs coefficient
reduction maps between these polynomial quotient rings.
-/

namespace SubexponentialSAT.LiftRing

noncomputable section

open Polynomial

section General

variable {R S : Type*} [CommRing R] [CommRing S]

theorem natCard_extension {F : R[X]} (hF : F.Monic) :
    Nat.card (Extension F) = Nat.card R ^ F.natDegree := by
  calc
    Nat.card (Extension F) = Nat.card (Fin F.natDegree → R) :=
      Nat.card_congr (coordinates hF).toEquiv
    _ = Nat.card R ^ F.natDegree := by rw [Nat.card_fun]; simp

end General

theorem decodeCount_natCast (p μ : ℕ) {F : (Base p μ)[X]}
    (hF : F.Monic) (hdeg : 0 < F.natDegree) (n : ℕ) (hn : n < p ^ μ) :
    decodeCount p μ hF (n : Lambda p μ F) = n := by
  have hcast : (n : Lambda p μ F) = of F (n : Base p μ) := by
    simp only [map_natCast]
  simp only [decodeCount, hcast, remainder_of hF hdeg, coeff_C_zero]
  exact ZMod.val_natCast_of_lt hn

end

end SubexponentialSAT.LiftRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_NilpotentDefect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Divisibility of the marked defect

After the input coordinates have been substituted, the coefficient of U in
each incidence argument is divisible by p. Polynomial operations preserve
the stronger invariant that the coefficient of U^j is divisible by p^j.
This proves the high-U vanishing needed by canonical truncation.
-/

namespace SubexponentialSAT.NilpotentDefect

noncomputable section

open scoped BigOperators

section Units

variable {R S : Type*} [CommRing R] [CommRing S]

theorem geometricInverse_mul (a b : R) (μ : ℕ)
    (hnil : (1 - a * b) ^ μ = 0) :
    geometricInverse a b μ * a = 1 := by
  rw [mul_comm]
  exact mul_geometricInverse a b μ hnil

end Units

end

end SubexponentialSAT.NilpotentDefect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpResidueInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable inversion by finite-field powering and nilpotent correction

The algorithm uses only scalar additions and multiplications, with explicit
finite loops. It constructs the entire inverse-difference table needed by CRT.
Its counters are ring-operation counts, not an assertion of machine time.
-/

namespace SubexponentialSAT.SubexpResidueInverse

open scoped BigOperators

section Algorithm

variable {A : Type*} [CommRing A]

theorem geometricHorner_value (z : A) (n : ℕ) :
    (geometricHornerWithCost z n).1 = ∑ i ∈ Finset.range n, z ^ i := by
  induction n with
  | zero => simp [geometricHornerWithCost]
  | succ n ih => simpa [geometricHornerWithCost, ih] using (@geom_sum_succ A _ z n).symm

theorem inverseWithCost_value (q μ : ℕ) (a : A) :
    (inverseWithCost q μ a).1 =
      NilpotentDefect.geometricInverse a (a ^ (q - 2)) μ := by
  simp only [inverseWithCost, SubexpPolynomialCost.scalarPower_value,
    geometricHorner_value, NilpotentDefect.geometricInverse]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

end Algorithm

section Correctness

variable {A E : Type*} [CommRing A] [Field E] [Fintype E]

/-- A finite-field Fermat power is an inverse after reduction. -/
theorem residue_fermat_inverse (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (a : A) (ha : ρ a ≠ 0) :
    ρ (a * a ^ (q - 2)) = 1 := by
  have hq2 : 2 ≤ q := by
    rw [← hq]
    exact Fintype.one_lt_card
  rw [map_mul, map_pow, ← pow_succ']
  have he : q - 2 + 1 = q - 1 := by omega
  rw [he, ← hq]
  exact FiniteField.pow_card_sub_one_eq_one (ρ a) ha

/-- The principal-kernel condition converts the residue defect into a
nilpotent element of the original, possibly non-field ring. -/
theorem fermat_defect_nilpotent (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x) (a : A) (ha : ρ a ≠ 0) :
    (1 - a * a ^ (q - 2)) ^ μ = 0 := by
  have hz : ρ (1 - a * a ^ (q - 2)) = 0 := by
    rw [map_sub, map_one, residue_fermat_inverse ρ q hq a ha, sub_self]
  obtain ⟨d, hd⟩ := hker _ hz
  rw [hd, mul_pow, hπ, zero_mul]

theorem inverseWithCost_correct (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x) (a : A) (ha : ρ a ≠ 0) :
    (inverseWithCost q μ a).1 * a = 1 := by
  rw [inverseWithCost_value]
  exact NilpotentDefect.geometricInverse_mul a (a ^ (q - 2)) μ
    (fermat_defect_nilpotent ρ q hq π μ hπ hker a ha)

end Correctness

end SubexponentialSAT.SubexpResidueInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalFactorAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Algebraic interfaces for constructing a local CRT factor from node
differences and inverting its constant coefficient. -/

namespace SubexponentialSAT.SubexpLocalFactorAlgebra

open Polynomial
open scoped BigOperators

variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

theorem localFactor_coeff_zero (θ : ι → A) (D : ℕ) (i : ι) :
    (TruncatedInverse.localFactor θ D i).coeff 0 =
      ∏ j ∈ Finset.univ.erase i, (θ i - θ j) ^ D := by
  simp only [TruncatedInverse.localFactor, coeff_zero_eq_eval_zero, eval_comp,
    eval_add, eval_X, eval_C, zero_add, JetCRT.cofactor, eval_prod,
    JetCRT.nodePower, eval_pow, eval_sub]

theorem residue_localFactor_coeff_ne_zero {E : Type*} [Field E]
    (ρ : A →+* E) (θ : ι → A)
    (hθ : Function.Injective (fun i => ρ (θ i))) (D : ℕ) (i : ι) :
    ρ ((TruncatedInverse.localFactor θ D i).coeff 0) ≠ 0 := by
  rw [localFactor_coeff_zero, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [map_pow, map_sub]
  apply pow_ne_zero
  intro h
  have hij := hθ (sub_eq_zero.mp h)
  exact (Finset.mem_erase.mp hj).1 hij.symm

/-- Truncating the local factor retains a nonzero residue at its constant
coefficient. This discharges the input condition of the scalar inverse. -/
theorem residue_truncated_localFactor_coeff_ne_zero {E : Type*} [Field E]
    (ρ : A →+* E) (θ : ι → A)
    (hθ : Function.Injective (fun i => ρ (θ i))) (D : ℕ) (hD : 0 < D) (i : ι) :
    ρ ((Truncation.trunc D (TruncatedInverse.localFactor θ D i)).coeff 0) ≠ 0 := by
  simpa only [Truncation.coeff_trunc, ite_eq_left hD] using
    residue_localFactor_coeff_ne_zero ρ θ hθ D i

end SubexponentialSAT.SubexpLocalFactorAlgebra

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalCorrectionAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Semantic invariants for the fixed-width local CRT preparation. Every
intermediate polynomial product may be truncated to D coefficients. The
constant coefficient is inverted once by the executable residue algorithm. -/

namespace SubexponentialSAT.SubexpLocalCorrectionAlgebra

open Polynomial
open scoped BigOperators

section ConstantInverse

variable {A E ι : Type*} [CommRing A] [Field E] [Fintype E]
variable [Fintype ι] [DecidableEq ι]

/-- The computed inverse of the truncated local factor's constant term is
also the exact constant inverse required by the established CRT formula. -/
theorem computed_constantInverse (ρ : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (π : A) (μ : ℕ) (hπ : π ^ μ = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (θ : ι → A) (hθ : Function.Injective (fun i => ρ (θ i)))
    (D : ℕ) (hD : 0 < D) (i : ι) :
    (SubexpResidueInverse.inverseWithCost q μ
      ((Truncation.trunc D (TruncatedInverse.localFactor θ D i)).coeff 0)).1 *
        (TruncatedInverse.localFactor θ D i).coeff 0 = 1 := by
  have h := SubexpResidueInverse.inverseWithCost_correct ρ q hq π μ hπ hker
    ((Truncation.trunc D (TruncatedInverse.localFactor θ D i)).coeff 0)
    (SubexpLocalFactorAlgebra.residue_truncated_localFactor_coeff_ne_zero ρ θ hθ D hD i)
  simpa only [Truncation.coeff_trunc, ite_eq_left hD] using h

end ConstantInverse

end SubexponentialSAT.SubexpLocalCorrectionAlgebra

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

theorem decodeCount_natCast (ht : 0 < t) (hd : d ≠ 0) (n : ℕ) (hn : n < 3 ^ t) :
    a.decodeCount t ht (n : a.O t) = n :=
  LiftRing.decodeCount_natCast 3 t (a.F_monic t ht) (by rw [a.F_degree t ht]; omega) n hn

theorem residue_cardinality : Nat.card a.E = 3 ^ d := by
  simpa only [a.residuePolynomial_degree, Nat.card_zmod] using
    LiftRing.natCard_extension a.residuePolynomial_monic

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLocalValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical local factor and correction have the canonical Hermite
meaning independently of the encoded representative of their head word. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

open SubexponentialSAT Polynomial
open SubexpSymbolicCost DensePolynomialProgram
open CRTLocalProgram

variable {B d J Q : ℕ} {R : Type*} [CommRing R]

theorem inverse_correct {E : Type*} [Field E] [Fintype E]
    (rho : R →+* E) (theta : Fin Q → R) (q : ℕ) (hq : Fintype.card E = q)
    (pi : R) (t : ℕ) (hpi : pi^t = 0) (hker : ∀ x, rho x = 0 → pi ∣ x)
    (hnodes : Function.Injective (fun i => rho (theta i))) (J : ℕ) (hJ : 0 < J) (i : Fin Q) :
    inverse theta q t J i * (TruncatedInverse.localFactor theta J i).coeff 0 = 1 :=
  SubexpLocalCorrectionAlgebra.computed_constantInverse rho q hq pi t hpi hker theta hnodes J hJ i

end SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramResult
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact semantic readback for the scalar returned by the native CRT loop,
in the ring defined by the actual searched polynomial. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT Polynomial

variable {d : ℕ} (model : RingModel.Data d) (t : ℕ) (ht : 0 < t)

/-- Scalar readback is exact under the independently chosen p-adic precision. -/
theorem scalar_decode_count (hd : d ≠ 0) (output : model.O t)
    (count m n : ℕ) (hcount : count ≤ m * 2^n) (hprecision : m * 2^n < 3^t)
    (hout : output = (count : model.O t)) :
    model.decodeCount t ht output = count := by
  rw [hout]
  exact model.decodeCount_natCast t ht hd count (hcount.trans_lt hprecision)

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Correctness of one fixed native bit program for exact count recovery from
physically stored Hasse jets over the actual searched ring model. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

theorem program_correct_oai (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input) scalarWidth frame)
    (hclean : ∀ j ∈ NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t)
    (hdistinct : Function.Injective (fun i => a.rho t ht
      ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
    (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
    (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
      nodes J (fun i => (jets i).1) target)
    (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
    (htarget : target.eval 0 = (count : a.O t)) :
    ∃ (b : Coeff t d) (rf : Fin 16 → Bool),
      RunsIn program (budget Q J t d (input.stacks 194).length (input.stacks 202).length + 1)
        (input.withPC (some program.entry))
        ((⟨rf, Function.update (Entry.prepared input.stacks) 261 (RingProgram.flat b)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode b = (count : a.O t) ∧
      a.decodeCount t ht ((RingProgram.modelRing t ht hd a M cache).decode b) = count := by
  let ops := RingProgram.modelRing t ht hd a M cache
  let theta := fun i => ops.decode (nodes i)
  let inverse := LocalValue.inverse theta (3^d) t J
  obtain ⟨steps, hsteps, out, b, he, hout, hvalue⟩ := command_value t ht hd a M cache hcanon hzbits
    J hJpos hB nodes jets minusOne hminus input hscalar scalarWidth frame hpoly hclean
    hzero hone hneg hJ hnodes hjets hexponent hprecision
  have hi : ∀ i, inverse i * (TruncatedInverse.localFactor theta J i).coeff 0 = 1 := by
    intro i
    exact LocalValue.inverse_correct (a.rho t ht) theta (3^d)
      (by simpa only [Nat.card_eq_fintype_card] using a.residue_cardinality)
      (3 : a.O t) t (a.prime_power_zero t)
      (fun x hx => (a.rho_eq_zero_iff t ht x).mp hx) hdistinct J hJpos i
  have hv : ops.decode b = (count : a.O t) := by
    rw [hvalue, scalar_value_eq_target a t ht theta J hJpos hdistinct inverse
      (fun i => CRTLocalProgram.Model.denote ops.decode (jets i)) hi target hdegree htargetJets,
      htarget]
  have heq : out = (⟨out.regs, Function.update (Entry.prepared input.stacks) 261 (RingProgram.flat b)⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hout
  rw [heq] at he
  refine ⟨b, out.regs, ?_, hv, ?_⟩
  · exact ⟨steps+1, Nat.add_le_add_right hsteps 1, compiled_halt_trace he 256 261⟩
  · exact scalar_decode_count a t ht hd.ne' (ops.decode b) count m n hcount hlarge hv

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct_oai
