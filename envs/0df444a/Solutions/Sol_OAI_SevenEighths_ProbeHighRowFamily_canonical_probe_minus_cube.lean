-- Prove2me | solution 1 for OAI.SevenEighths.ProbeHighRowFamily.canonical_probe_minus_cube
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:49:19.22796+00:00
-- url     : https://prove2.me/submissions/07b7c5fe-c4db-4ac9-805f-71a2e4cd069a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_canonical_large_original_tail
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_finite_cube_arbitrary_saving
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_small_original_physical_tail
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_compensatedRowTripleIntegral_eq_tsum
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_compensatedTuple_eq_source_triple
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_rowIntegral_summable

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ActualEisensteinCoordinates

theorem eval_congr_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    ∃ z : O, eval a b - eval c d = 4 * z := by
  have ha4 : (4 : ℤ) ∣ a-c := (ZMod.intCast_eq_intCast_iff_dvd_sub c a 4).mp ha.symm
  have hb4 : (4 : ℤ) ∣ b-d := (ZMod.intCast_eq_intCast_iff_dvd_sub d b 4).mp hb.symm
  obtain ⟨u, hu⟩ := ha4
  obtain ⟨v, hv⟩ := hb4
  refine ⟨(u : O) + (v : O) * omega, ?_⟩
  dsimp [eval]
  rw [show a = c + 4*u by omega, show b = d + 4*v by omega]
  push_cast
  ring

theorem congr_mod_four_of_residue_eq {x y : O}
    (h : residue x = residue y) : ∃ z : O, x-y = 4*z := by
  rw [←eval_coords x, ←eval_coords y]
  apply eval_congr_mod_four
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem residue_lift (v : EisensteinEPrimaryPhase.Coord) :
    residue (lift v) = v := by
  simp [lift, residue_eval]

end ActualEisensteinCoordinates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical

namespace FiniteGaussPhase

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

end FiniteGaussPhase

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

open scoped BigOperators Classical

namespace QuadraticGaussRay

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem fixed_two_mk_eq_residue_lift (c : O) :
    Ideal.Quotient.mk cubicTwoIdeal c =
      Ideal.Quotient.mk cubicTwoIdeal (lift (residue c)) := by
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq (residue_lift (residue c)).symm
  apply Ideal.Quotient.eq.mpr
  rw [cubicTwoIdeal, Ideal.mem_span_singleton]
  refine ⟨(-2 : O) * z, ?_⟩
  calc
    c - lift (residue c) = 4 * z := hz
    _ = (-2 : O) * (-2 * z) := by ring

end QuadraticGaussRay

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Poisson
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
open CompletedGauss ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubicExponent_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (negative : Bool) :
    actualSextic P hg ^ cubicExponent negative ≠ 1 := by
  let χ := actualSextic P hg ^ 2
  have hχ : χ ≠ 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg]
    exact (MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr (cubicChar_ne_one P hg)
  have h3 : χ ^ 3 = 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg, MulChar.ringHomComp_pow, cubicChar_pow_three P hg, MulChar.ringHomComp_one]
  have h2 : χ ^ 2 ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = χ ^ 2 * χ := by rw [h, one_mul]
      _ = χ ^ 3 := (pow_succ χ 2).symm
      _ = 1 := h3
  cases negative with
  | false => simpa only [cubicExponent, Bool.false_eq_true, ite_false,
      ] using hχ
  | true =>
      have he : actualSextic P hg ^ 4 = χ ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      simpa only [cubicExponent, ite_true, he] using h2

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.GaussNorm
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem gaussTwo_norm_one (I : Ideal O) (hI : Admissible I) : ‖gaussTwo I hI.2‖ = 1 := by
  let c := primaryGenerator I
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Fintype (O ⧸ P.val) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Field (O ⧸ P.val) := Ideal.Quotient.field P.val
  have hc : Ideal.span {c} = ∏ P : PrimeIndex I, P.val :=
    (primaryGenerator_spec I hI.2).1.trans (primeIndex_product I hI).symm
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ P : PrimeIndex I, O ⧸ P.val :=
    (Ideal.quotEquivOfEq hc).trans
      (IdealGaussCRT.quotientProdEquivPi (fun P : PrimeIndex I => P.val)
        (CanonicalRowCompletion.primeIndex_pairwise_coprime I))
  let χ : ∀ P : PrimeIndex I, MulChar (O ⧸ P.val) ℂ :=
    fun P => actualSextic P.val (primeIndex_good I hI.2 P) ^ 2
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hI.2
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hI.2
  have hχ : ∀ P : PrimeIndex I, χ P ≠ 1 := fun P =>
    cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) false
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun P : PrimeIndex I => O ⧸ P.val)
    e χ ψ hχ (fun P => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun P : PrimeIndex I => O ⧸ P.val) e ψ hψ P)
  have hrow (x : O ⧸ Ideal.span {c}) : (∏ P : PrimeIndex I, χ P (e x P)) =
      CompletedGauss.cubicRow I hI.2 ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) x) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    dsimp only [c] at z ⊢
    simp only [e, c, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      IdealGaussCRT.quotientProdEquivPi_mk, CompletedGauss.cubicRow_mk, χ]
  simp_rw [hrow] at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  have hnorm := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq
  change ‖(∑ x : O ⧸ Ideal.span {c},
    CompletedGauss.cubicRow I hI.2 ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) x) * ψ x) /
    (‖eisEmbedding c‖ : ℂ)‖ = 1
  rw [norm_div, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hI.2))

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Completed
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompleted
open ActualEisensteinCubic CompletedGauss
open RayFourExpansion QuadraticGaussRay SecondPassArithmetic

local notation "O" => ActualEisensteinCubic.O

theorem completedMask_norm_le_one (S : Finset (Ideal O)) (D I J : Ideal O) :
    ‖completedMask S D I J‖ ≤ 1 := by
  unfold completedMask
  split_ifs <;> norm_num

end SevenEighths.ProbeCompleted
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Row
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

end SevenEighths.ProbeRow
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalFourier
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

theorem rawFourier_norm_le (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (H : O) :
    ‖rawFourier a ha F H‖ ≤ (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  rw [rawFourier, tsum_fintype]
  calc
    _ ≤ ∑ m : O ⧸ Ideal.span {a}, ‖F m * quotientTrace a ha (Ideal.Quotient.mk _ H*m)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m : O ⧸ Ideal.span {a}, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact hF m
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem congruenceCoefficient_norm_le (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (hχ : ∀ d, ‖χ d‖≤1) (H : O) :
    ‖congruenceCoefficient a s ha F χ H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) * (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold congruenceCoefficient
  rw [tsum_fintype]
  calc
    _ ≤ ∑ d : O ⧸ Ideal.span {s}, ‖χ d *
        (if h : s ∣ H-a*representative s d then
          rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _d : O ⧸ Ideal.span {s}, (Ideal.absNorm (Ideal.span {a}):ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · rw [norm_mul]
        exact (mul_le_mul (hχ d) (rawFourier_norm_le a ha F hF _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · simp only [mul_zero, norm_zero]
        positivity
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem CalibrationData.residueMonoid_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhaseCancellation
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem quadraticRayValue_norm_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : ‖quadraticRayValue r‖ = 1 := by
  rw [quadraticRayValue_eq_fourthRoot r hr]
  simp [fourthRoot]

theorem G_norm_one (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : ‖G a‖ = 1 := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (by decide : (3 : ℕ) ≠ 0)
  change ‖fixedGValue (residue a)‖ = 1
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift, norm_mul, norm_inv,
    hn, inv_one, one_mul]
  exact quadraticRayValue_norm_one _ ha

theorem cubicTwo_isUnit_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    IsUnit (Ideal.Quotient.mk cubicTwoIdeal a) := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hd : (2 : O) ∣ a := by
    simpa only [cubicTwoIdeal, Ideal.mem_span_singleton, neg_dvd] using hm
  exact ((odd_residue_iff_not_two_dvd a).mp ha) hd

theorem G_norm_one_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) : ‖G a‖ = 1 :=
  G_norm_one a ha (cubicTwo_isUnit_of_odd a ha)

end SevenEighths.ProbePhase
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SourceBounds
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbePhase ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareCongruenceCoefficient_norm_le (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    ‖bareCongruenceCoefficient A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  apply congruenceCoefficient_norm_le A s hA hs
  · intro m
    exact idealRowHom_norm _ _
  · intro m
    exact idealRowHom_norm _ _

theorem bareSourceCoefficient_norm_le (η : HeckeFamily.Character)
    (I : Ideal O) (hI : CubicSieve.Admissible I) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) (H : O) :
    ‖bareSourceCoefficient η I hI.2 A s (supportedElement_ne_zero A hA) H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  have hR : ‖reciprocitySign A s‖≤1 := sexticReciprocityPhase_norm A s
  have ht := targetMonoid_norm_le_one η A
  have hfac : ‖targetMonoid η A‖*‖reciprocitySign A s‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) ht).trans hR
  calc
    _ = (‖targetMonoid η A‖*‖reciprocitySign A s‖)*
        ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
      simp only [bareSourceCoefficient, correctedFiniteCoefficient, reciprocityCoefficient,
        norm_mul,norm_star,CubicSieve.gaussTwo_norm_one I hI,
        FiniteGaussPhase.norm_angularFactor A (supportedElement_ne_zero A hA),
        G_norm_one_of_odd A (supported_residue_odd A hA),one_mul,mul_one]
      ring
    _ ≤ ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hfac
    _ ≤ _ := bareCongruenceCoefficient_norm_le A s (supportedElement_ne_zero A hA)
      (supportedElement_ne_zero s hs) H

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighSeries
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem bareIdealHighCoefficient_norm_le (η : HeckeFamily.Character) (u : O) (I J K L : Id) :
    ‖bareIdealHighCoefficient η u I J K L‖ ≤ (K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3 := by
  unfold bareIdealHighCoefficient
  split_ifs with h
  · have hi := (supported_span_primaryGenerator_iff I).mpr h.2.1
    have hj := (supported_span_primaryGenerator_iff J).mpr h.2.2.1
    have hk := (supported_span_primaryGenerator_iff K).mpr h.2.2.2.1
    have hb := bareSourceCoefficient_norm_le η I ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      (primaryGenerator I*primaryGenerator J^3) (primaryGenerator K)
      (supported_completed _ _ hi hj) hk (u*primaryGenerator L^6)
    rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).1,
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).1,
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).1,
      map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] at hb
    convert (preTransparency := .instances) hb using 1 ; ring
  · simp only [norm_zero]
    positivity

lemma fullIdealWeight_nat_scale (s : ℂ) (I : Id) (hI : I≠0) (k : ℕ) :
    (I.absNorm:ℝ)^k * ‖fullIdealWeight s I‖ = ‖fullIdealWeight (s-k) I‖ := by
  have hN : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [fullIdealWeight,if_neg hI]
  simp only [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re]
  rw [← Real.rpow_natCast,← Real.rpow_add hN]
  congr 1
  ring

theorem bareIdealHighSummand_norm_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖bareIdealHighSummand η u x w z I J K L‖ ≤
      ‖fullIdealWeight (x-1/2) I‖ * ‖fullIdealWeight (3*x-2) J‖ *
      ‖fullIdealWeight (w-1) K‖ * ‖fullIdealWeight (6*z) L‖ := by
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L
  · have hb := bareIdealHighCoefficient_norm_le η u I J K L
    calc
      _ ≤ ((K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3) *
          ‖fullIdealWeight (x+1/2) I‖ * ‖fullIdealWeight (1+3*x) J‖ *
          ‖fullIdealWeight w K‖ * ‖fullIdealWeight (6*z) L‖ := by
        simp only [bareIdealHighSummand,norm_mul]
        gcongr
      _ = ((I.absNorm:ℝ)^1*‖fullIdealWeight (x+1/2) I‖) *
          ((J.absNorm:ℝ)^3*‖fullIdealWeight (1+3*x) J‖) *
          ((K.absNorm:ℝ)^1*‖fullIdealWeight w K‖) * ‖fullIdealWeight (6*z) L‖ := by ring
      _ = _ := by
        rw [fullIdealWeight_nat_scale _ I h.2.1.1 1,
          fullIdealWeight_nat_scale _ J h.2.2.1.1 3,
          fullIdealWeight_nat_scale _ K h.2.2.2.1.1 1]
        norm_num only [Nat.cast_one, Nat.cast_ofNat]
        rw [show x+(1/2:ℂ)-1=x-1/2 by ring,show (1:ℂ)+3*x-3=3*x-2 by ring]
  · simp only [bareIdealHighSummand,bareIdealHighCoefficient,dif_neg h,zero_mul,norm_zero]
    positivity

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighDeletion
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highIdealMask_norm_le_one (S : Finset Id) (D I J K L : Id) :
    ‖highIdealMask S D I J K L‖≤1 := by
  unfold highIdealMask
  split_ifs <;> simp only [mul_one,mul_zero,norm_zero]
  · exact completedMask_norm_le_one S D I J
  all_goals norm_num

lemma markedIdealHighSummand_norm_le (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖markedIdealHighSummand S D η u x w z I J K L‖≤‖bareIdealHighSummand η u x w z I J K L‖ := by
  rw [markedIdealHighSummand,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (highIdealMask_norm_le_one S D I J K L)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighAbsolute
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma frequencyWeight_norm (z : ℂ) (u : NonzeroFrequency) :
    ‖frequencyWeight z u‖=‖eisEmbedding u.val‖^(-2*z.re) := by
  have hn : 0<‖eisEmbedding u.val‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero u.property)
  unfold frequencyWeight elementNorm
  have hN : (Ideal.absNorm (Ideal.span {u.val}):ℝ)=‖eisEmbedding u.val‖^2 :=
    (eisEmbedding_norm_sq_eq_absNorm_span u.val).symm
  rw [hN,
    Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn), Complex.neg_re,
    ← Real.rpow_natCast_mul hn.le 2]
  congr 1
  ring

theorem frequencyWeight_summable_norm (z : ℂ) (hz : 1<z.re) :
    Summable (fun u : NonzeroFrequency => ‖frequencyWeight z u‖) := by
  simp only [frequencyWeight_norm]
  exact (summable_embedding_rpow (-2*z.re) (by linarith)).subtype _

lemma highAbsoluteMajorant_nonneg (x w z : ℂ) (p : (Id×Id)×(Id×Id)) :
    0≤highAbsoluteMajorant x w z p := by unfold highAbsoluteMajorant; positivity

lemma highAbsoluteMajorant_summable (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) : Summable (highAbsoluteMajorant x w z) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by norm_num [Complex.sub_re,Complex.div_re]; linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by norm_num [Complex.sub_re,Complex.mul_re]; linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by norm_num [Complex.mul_re]; linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  unfold highAbsoluteMajorant
  simpa only [mul_assoc] using hall

theorem fullHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re)
    (mask : NonzeroFrequency→ℂ) (hmask : ∀u,‖mask u‖≤1) :
    Summable (fun p : NonzeroFrequency×((Id×Id)×(Id×Id)) =>
      mask p.1 * frequencyWeight z p.1 *
        markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) := by
  have hm := (frequencyWeight_summable_norm z hz).mul_of_nonneg
    (highAbsoluteMajorant_summable x w z hx hw (by linarith))
    (fun _=>norm_nonneg _) (highAbsoluteMajorant_nonneg x w z)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hm
  intro p
  rw [norm_mul,norm_mul]
  have hcoeff := (markedIdealHighSummand_norm_le S D η p.1.val x w z
    p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  change _≤‖frequencyWeight z p.1‖*highAbsoluteMajorant x w z p.2
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hmask p.1) (norm_nonneg _)
      · exact hcoeff
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [one_mul]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma elementNorm_mul (a b : ActualEisensteinCubic.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RadialIdentity
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma elementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.TupleScaling
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma tuple_norm_pos {K : ℕ} (p : Fin K→ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) : 0<elementNorm (∏i∈J,p i) := by
  apply elementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.TupleProducts
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

lemma tuple_norm_cpow {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0)
    (J : Finset (Fin K)) (s : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^s=∏i∈J,(elementNorm (p i):ℂ)^s := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,elementNorm_one,Complex.ofReal_one,Complex.one_cpow]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,elementNorm_mul,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (elementNorm_pos _ (hp i)).le (tuple_norm_pos p hp J).le,
      ih,Finset.prod_insert hi]

lemma tuple_target_star {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) :
    star (HeckeFamily.elementCoeff η (∏i∈J,p i))=∏i∈J,star (HeckeFamily.elementCoeff η (p i)) := by
  change star (ProbeRow.targetMonoid η (∏i∈J,p i))=_
  rw [map_prod,star_prod]
  rfl

lemma tuple_source_scalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (x w z : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)=
    (∏i,(elementNorm (p i):ℂ)^(z-1))*
      (∏i∈J,(elementNorm (p i):ℂ)^(-w))*
      (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x) := by
  rw [tuple_norm_cpow p hp J,tuple_norm_cpow p hp (Finset.univ\J),tuple_target_star]
  have he (i : Fin K) : (elementNorm (p i):ℂ)^(z-w-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^(-w) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  have hf (i : Fin K) : (elementNorm (p i):ℂ)^(x+z-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^x := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  simp only [he,hf,Finset.prod_mul_distrib]
  have hc := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i : Fin K=>(elementNorm (p i):ℂ)^(z-1))
  rw [←hc]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.TupleRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceRowSummand_summable (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (D : Id) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    Summable (fun u : FreeRow=>star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S D η u.val x w z) := by
  let e : FreeRow×((Id×Id)×(Id×Id))→FullHighIndex := fun p=>(⟨p.1.val,p.1.property.1⟩,p.2)
  have he : Function.Injective e := by
    intro a b h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun t : FullHighIndex=>t.1.val) h
    · exact congrArg (fun t : FullHighIndex=>t.2) h
  have hs := (fullHighSummand_summable S D η x w z hx hw hz
    (fun H=>star (C.residueMonoid H.val))
    (fun H=>by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val)).comp_injective he
  have ht := hs.prod
  apply ht.congr
  intro u
  dsimp only [Function.comp_def,e]
  exact tsum_mul_left (a:=star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩)
    (f:=fun c : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u.val x w z c.1.1 c.1.2 c.2.1 c.2.2)

lemma tupleSourceSeries_common_scale {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
          sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z := by
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_source_scalar η p hp J x w z
  unfold tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*he*
    sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

theorem tupleSourceSeries_eq_rows {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
          indexedCompensatedHigh η S p u.val x w z := by
  rw [tupleSourceSeries_common_scale η S C p hp]
  congr 1
  let f : Finset (Fin K)→FreeRow→ℂ := fun J u=>tupleIndexedCoefficient η p J x w*
    (star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u.val x w z)
  have hf (J : Finset (Fin K)) : Summable (f J) :=
    (sourceRowSummand_summable η S C _ x w z hx hw hz).mul_left _
  have hsum := Summable.tsum_finsetSum (s:=(Finset.univ:Finset (Fin K)).powerset)
    (f:=f) (fun J _=>hf J)
  unfold sourceRowSeries
  simp only [←tsum_mul_left]
  change (∑J∈(Finset.univ:Finset (Fin K)).powerset,∑'u,f J u)=_
  rw [←hsum]
  apply tsum_congr
  intro u
  unfold indexedCompensatedHigh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [f]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.TuplePrime
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CanonicalSlots
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sum_canonical_element_tuples {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),F (fun i=>primaryGenerator (P i).val.val) := by
  exact ((canonicalTupleEquiv T hT).sum_comp (fun p=>F (fun i=>(p i).val))).symm

theorem sum_canonical_weighted_tuples {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),
      (∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Y i))*
        F (fun i=>primaryGenerator (P i).val.val) := by
  rw [sum_canonical_element_tuples T hT (fun p=>(∏i,W i (elementNorm (p i)/Y i))*F p)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [primaryTuple_norm (P _).val (hT _ _ (P _).property)]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
namespace OAI

noncomputable section
open scoped Classical Topology
open Set
namespace SevenEighths.HeckeLogarithmicInput
open HeckeFamily

theorem modulus_norm_ge_one (η : Character) : 1 ≤ (η.modulus.absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

end SevenEighths.HeckeLogarithmicInput

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.FirstTail
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
local notation "O" => HeckeFamily.O

theorem firstPrimeDefectBound_summable (eps : ℝ) (heps : 0<eps) :
    Summable (firstPrimeDefectBound eps) := by
  have ht : 1<(1+min eps (1/50:ℝ) : ℂ).re := by
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re]
    have hm : 0< min eps (1/50:ℝ) := lt_min heps (by norm_num)
    linarith
  have h := (CubicEisenstein.fullIdealWeight_summable_norm
    (1+min eps (1/50:ℝ) : ℂ) ht).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight (1+min eps (1/50:ℝ) : ℂ) P.val‖=_
  unfold firstPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp only [Complex.neg_re,Complex.add_re,Complex.one_re,Complex.ofReal_re]
  congr 2
  ring

theorem FirstTail.summable {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S) :
    Summable (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val) :=
  (firstPrimeDefectBound_summable eps h.positive).subtype _

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CompensatedTriple
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma tupleSourceTripleIntegral_eq_rows {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O)
    (hp : ∀i,p i≠0) (X Y Z : ℝ) :
    tupleSourceTripleIntegral η S C W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S C W0 W1 p X Y Z := by
  unfold tupleSourceTripleIntegral compensatedRowTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact tupleSourceSeries_eq_rows η S C p hp
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

theorem compensatedTuple_eq_row_triple {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  rw [compensatedTuple_eq_source_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    p hp X Y Z hX hY hZ,tupleSourceTripleIntegral_eq_rows η S _ W0 W1 p hp]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalSplit
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

local instance instCountableO_8_rd27490_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
attribute [local instance] OAI.SevenEighths.ProbePhysical.instMeasurableSpaceFreeRow_1
local instance instMeasurableSingletonClassFreeRow_1_rd27490_1 : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩
lemma rowIntegral_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    rowIntegral η S C p W0 W1 X Y Z principalFreeRow=principalRowIntegral η S p W0 W1 X Y Z := by
  simp only [rowIntegral,principalRowIntegral,compensatedRowOnLines,principalFreeRow,
    frequencyWeight,elementNorm_one,map_one,star_one,Complex.ofReal_one,Complex.one_cpow,one_mul]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CanonicalPhysicalRows
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem compensatedPhysicalProbe_canonical_slots {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        compensatedTuple η C W0 W1 (fun i=>primaryGenerator (P i).val.val) X Y Z :=
  sum_canonical_weighted_tuples T hT W Yp (fun p=>compensatedTuple η C W0 W1 p X Y Z)

theorem compensatedPhysicalProbe_eq_canonical_rows {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑'u : FreeRow,∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
  have hn (P : ∀i,↥(T i)) (i : Fin K) : primaryGenerator (P i).val.val≠0 :=
    supported_primaryGenerator_ne_zero _ (hT i _ (P i).property)
  have hs (P : ∀i,↥(T i)) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  rw [compensatedPhysicalProbe_canonical_slots η _ W0 W1 T hT W Yp]
  calc
    _ = ∑P : (∀i,↥(T i)),∑'u : FreeRow,(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
      rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
          _ (hn P) X Y Z hX hY hZ,
          compensatedRowTripleIntegral_eq_tsum η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
        exact tsum_mul_left.symm
    _ = _ := (Summable.tsum_finsetSum (fun P _=>hs P)).symm

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma rowNorm_ge_one (u : FreeRow) : 1≤ rowNorm u := by
  unfold rowNorm
  have hn : (Ideal.span {u.val}:Ideal O)≠⊥ := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn)

theorem tsum_dyadicRows (A : ℝ) (hA : 0<A) (f : FreeRow→ℂ) (hf : Summable f) :
    Summable (fun n=>∑u∈dyadicRows A n,f u) ∧
      (∑'u : FreeRow,if u.val≠1 ∧ A≤ rowNorm u then f u else 0)=
        ∑'n : ℕ,∑u∈dyadicRows A n,f u := by
  let e := dyadicRowEquiv A hA
  have hs : Summable (fun p : Σn : ℕ,dyadicRows A n=>f p.2.val) :=
    e.summable_iff.mpr (hf.subtype (fun u=>u.val≠1 ∧ A≤ rowNorm u))
  have heq : (fun n : ℕ=>∑'u : dyadicRows A n,f u.val)=(fun n=>∑u∈dyadicRows A n,f u) := by
    funext n
    exact Finset.tsum_subtype _ _
  refine ⟨by simpa only [heq] using hs.sigma,?_⟩
  calc
    _ = ∑'u : {u : FreeRow // u.val≠1 ∧ A≤ rowNorm u},f u.val := by
      have hh := (tsum_subtype {u : FreeRow | u.val≠1 ∧ A≤ rowNorm u} f).symm
      convert (preTransparency := .instances) hh using 1
      · apply tsum_congr
        intro u
        by_cases h : u.val≠1 ∧ A≤ rowNorm u
        · simp [h]
        · simp [h]
      · rfl
    _ = ∑'p : Σn : ℕ,dyadicRows A n,f p.2.val := (e.tsum_eq (fun u=>f u.val)).symm
    _ = _ := by rw [hs.tsum_sigma];simp_rw [Finset.tsum_subtype]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.SmallPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma smallDyadicRows_disjoint (L : ℝ) : Pairwise (fun m n=>Disjoint (smallDyadicRows L m) (smallDyadicRows L n)) := by
  intro m n hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma small_rows_biUnion (L : ℝ) :
    (smallDyadicIndices L).biUnion (smallDyadicRows L)=rowBand 1 L := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    have hh := mem_smallDyadicRows.mp hu
    have hm := mem_dyadicRows.mp hh.1
    exact mem_rowBand.mpr ⟨hm.1,rowNorm_ge_one u,hh.2⟩
  · intro hu
    have hh := mem_rowBand.mp hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u hh.1 hh.2.1
    refine Finset.mem_biUnion.mpr ⟨n,?_,mem_smallDyadicRows.mpr ⟨hn,hh.2.2⟩⟩
    rw [mem_smallDyadicIndices]
    have hlo := (mem_dyadicRows.mp hn).2.1
    simpa only [one_mul] using hlo.trans hh.2.2.le

lemma sum_small_dyadicRows (L : ℝ) (f : FreeRow→ℂ) :
    (∑u∈rowBand 1 L,f u)=∑n∈smallDyadicIndices L,∑u∈smallDyadicRows L n,f u := by
  rw [←small_rows_biUnion L]
  exact Finset.sum_biUnion (fun m hm n hn hmn=>smallDyadicRows_disjoint L hmn)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ExhaustivePartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

theorem nonprincipal_rows_partition (L U : ℝ) (hL : 1≤L) (hLU : L≤U)
    (f : FreeRow→ℂ) (hf : Summable f) :
    (∑'u : FreeRow,if u.val=1 then 0 else f u)=
      (∑n∈smallDyadicIndices L,∑u∈smallDyadicRows L n,f u)+
        (∑u∈rowBand L U,f u)+(∑'n : ℕ,∑u∈dyadicRows U n,f u) := by
  let g1 := (↑(rowBand 1 L):Set FreeRow).indicator f
  let g2 := (↑(rowBand L U):Set FreeRow).indicator f
  let g3 := {u : FreeRow | u.val≠1 ∧ U≤ rowNorm u}.indicator f
  have hg1 : Summable g1 := hf.indicator _
  have hg2 : Summable g2 := hf.indicator _
  have hg3 : Summable g3 := hf.indicator _
  have hpoint (u : FreeRow) : (if u.val=1 then 0 else f u)=g1 u+g2 u+g3 u := by
    have hnorm := rowNorm_ge_one u
    by_cases hu : u.val=1
    · simp [g1,g2,g3,mem_rowBand,hu]
    · by_cases hsmall : rowNorm u<L
      · have hU : ¬U≤ rowNorm u := not_le.mpr (hsmall.trans_le hLU)
        have hL' : ¬L≤ rowNorm u := not_le.mpr hsmall
        simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hU]
      · have hL' : L≤ rowNorm u := le_of_not_gt hsmall
        by_cases hlarge : U≤ rowNorm u
        · have hU : ¬rowNorm u<U := not_lt.mpr hlarge
          simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hlarge,hU]
        · have hU : rowNorm u<U := lt_of_not_ge hlarge
          simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hlarge,hU]
  have hsum1 : (∑'u,g1 u)=∑u∈rowBand 1 L,f u := by
    rw [tsum_eq_sum (s:=rowBand 1 L) (fun u hu=>Set.indicator_of_notMem hu f)]
    apply Finset.sum_congr rfl
    intro u hu
    exact Set.indicator_of_mem hu f
  have hsum2 : (∑'u,g2 u)=∑u∈rowBand L U,f u := by
    rw [tsum_eq_sum (s:=rowBand L U) (fun u hu=>Set.indicator_of_notMem hu f)]
    apply Finset.sum_congr rfl
    intro u hu
    exact Set.indicator_of_mem hu f
  have hsum3 : (∑'u,g3 u)=∑'n : ℕ,∑u∈dyadicRows U n,f u := by
    have hh := (tsum_dyadicRows U (by linarith) f hf).2
    convert (preTransparency := .instances) hh using 1
    apply tsum_congr
    intro u
    by_cases h : u.val≠1 ∧ U≤ rowNorm u <;> simp [g3,h]
  simp_rw [hpoint]
  rw [(hg1.add hg2).tsum_add hg3,hg1.tsum_add hg2,hsum1,hsum2,hsum3,sum_small_dyadicRows]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem physicalRowValue_summable {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Summable (physicalRowValue S hmax η T W Yp W0 W1 X Y Z) := by
  have hs (P : ∀i,T i) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (fun i=>supported_primaryGenerator_ne_zero _ (hT i _ (P i).property))
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  have hh (F : Finset (∀i,T i)) : Summable (fun u : FreeRow=>∑P∈F,
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert P F hP ih => simpa only [Finset.sum_insert hP] using (hs P).add ih
  exact hh Finset.univ

theorem canonical_physical_probe_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z L U : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hL : 1≤L) (hLU : L≤U) :
    compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      (∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)+
      ((∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W Yp W0 W1 X Y Z)+
        finitePhysicalRows S hmax η (rowBand L U) T W Yp W0 W1 X Y Z+
        (∑'n : ℕ,finitePhysicalRows S hmax η (dyadicRows U n) T W Yp W0 W1 X Y Z)) := by
  let f := physicalRowValue S hmax η T W Yp W0 W1 X Y Z
  have hf := physicalRowValue_summable S hmax η T hT W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [compensatedPhysicalProbe_eq_canonical_rows η S hmax hS.prime hS.bad ((by simp [fixedBadPrimes] : fixedBadPrimes.Nonempty).mono hS.bad) T hT W Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  change (∑'u,f u)=_
  rw [hf.tsum_eq_add_tsum_ite principalFreeRow]
  have heq : (fun u : FreeRow=>if u=principalFreeRow then 0 else f u)=
      (fun u : FreeRow=>if u.val=1 then 0 else f u) := by
    funext u
    have hu : u=principalFreeRow ↔ u.val=1 := by
      constructor
      · intro h;subst u;rfl
      · intro h;exact Subtype.ext h
    simp only [hu]
  rw [heq,nonprincipal_rows_partition L U hL hLU f hf]
  congr 1
  · dsimp [f,physicalRowValue]
    simp only [rowIntegral_principal]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalTails
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem canonical_small_original_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_original_physical_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  let L := Z^(1/100:ℝ)
  have hrows (n : ℕ) (hn : n∈smallDyadicIndices L) (u : FreeRow) (hu : u∈smallDyadicRows L n) :
      u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n := by
    have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
    exact ⟨hh.1,by simpa only [one_mul,rowNorm] using hh.2.1,by simpa only [one_mul,rowNorm] using hh.2.2.le⟩
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=>mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=>Z^(length i)) W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O

theorem canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨Cs,hCs,hs⟩ := canonical_small_original_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := canonical_large_original_tail K δ a b B ζ saving hδ (by linarith) hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=>outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=>Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/100:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n)
      T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z :=
    (sum_small_dyadicRows (Z^(1/100:ℝ)) (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=>by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by gcongr <;> linarith
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma FirstTail.mono_parameter {eps eps' : ℝ} {S : Finset (Ideal O)}
    (h : FirstTail eps S) (hle : eps≤eps') : FirstTail eps' S := by
  have hp : 0<eps' := h.positive.trans_le hle
  refine ⟨hp,h.norm_four,?_⟩
  apply le_trans _ h.small
  apply ((firstPrimeDefectBound_summable eps' hp).subtype _).tsum_le_tsum _ h.summable
  intro P
  unfold firstPrimeDefectBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le
  · have hn := h.norm_four P.val P.property
    exact_mod_cast (by omega : 1≤P.val.val.absNorm)
  · have hm := min_le_min_right (1/50:ℝ) hle
    linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeReduction
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem canonical_probe_minus_cube_oai (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (51/100:ℝ)≤alpha u ∧ alpha u≤1 ∧ 2<base u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u)<alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨C0,hC0,h0⟩ := canonical_probe_minus_central K e δ a b B ζ saving he he' hδ hδ' hζ ha hb hB hβ
    S hS hmax (hfirst.mono_parameter (by linarith)) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ B hτ hb hζ' hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis length hl0 hl hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis length hl0 hl W hWS hWB
  let R := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis length hl hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)
  have hE : 0≤E := by dsimp [E];positivity
  have hsave : Z^(-saving)≤E := by dsimp [E];have : 0≤Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.ProbeHighRowFamily.canonical_probe_minus_cube_oai.{u_1} := @OAI.SevenEighths.ProbeHighRowFamily.canonical_probe_minus_cube_oai.{u_1}
