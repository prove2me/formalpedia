-- Prove2me | solution 1 for MazurTransfer.original_rational_thirteen_support_finite_dimension_and_radicand_bound
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T20:26:39.096258+00:00
-- url     : https://prove2.me/submissions/955d6939-f1b7-4b82-b19a-0775f479cad7

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original rational nineteenth-power classes supported at thirteen inject into F19 through their thirteen-coordinate, giving finite dimension at most one. The same radicand injection criterion retains all support and injectivity hypotheses.
Named downstream consumer: the original selected pi Selmer radicand dimension theorem and rational norm quotient bound.
-/
import Definitions.Def_MazurTransfer_OriginalRationalThirteenSupportedPowerClassSubmoduleData20261019
import Theorems.Thm_MazurTransfer_original_rational_nineteenth_power_valuation_formula_and_zero_detection
noncomputable section
open MazurTransfer RationalNineteenthPowerClasses RationalNineteenthPowerValuations RationalThirteenPowerClassBound
attribute [local instance] MazurTransfer.RationalThirteenPowerClassBound.instModuleZModOfNatNatAdditivePowerClasses_rationalThirteenPowerClassBound
attribute [local instance] MazurTransfer.RationalThirteenPowerClassBound.instFactPrimeOfNatNat_rationalThirteenPowerClassBound
namespace MazurTransfer.RationalThirteenSupportDimensionProofBoundary20261019
end MazurTransfer.RationalThirteenSupportDimensionProofBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the genuine rational nineteenth-power classes whose
prime valuations vanish modulo nineteen outside thirteen form a finite
F19 subspace of dimension at most one. The coordinate at thirteen is
proved injective; no arithmetic property of an actual curve is assumed.
Named downstream consumer: restrict the checked actual pi Selmer radicand
injection after identifying its rational prime valuation conditions.
-/

noncomputable section
namespace MazurTransfer.OriginalRationalThirteenSupportFiniteDimensionProof20261019
open MazurTransfer.RationalThirteenPowerClassBound
open RationalNineteenthPowerClasses RationalNineteenthPowerValuations
attribute [local instance] MazurTransfer.RationalThirteenPowerClassBound.instFactPrimeOfNatNat_rationalThirteenPowerClassBound
attribute [local instance] MazurTransfer.RationalThirteenPowerClassBound.instModuleZModOfNatNatAdditivePowerClasses_rationalThirteenPowerClassBound



theorem mem_thirteenSupport (x : Additive PowerClasses) :
    x ∈ thirteenSupport ↔ ∀ (q : ℕ) (hq : q.Prime), q ≠ 13 → valuationLinearMap q hq x = 0 := by
  simp only [thirteenSupport, Submodule.mem_iInf, LinearMap.mem_ker]



theorem thirteenCoordinate_injective : Function.Injective thirteenCoordinate := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply MazurTransfer.original_rational_nineteenth_power_valuation_formula_and_zero_detection.2.2 (x.val - y.val)
  intro q hq
  by_cases h13 : q = 13
  · subst q
    rw [map_sub]
    exact sub_eq_zero.mpr h
  · rw [map_sub, (mem_thirteenSupport x.val).mp x.property q hq h13,
      (mem_thirteenSupport y.val).mp y.property q hq h13, sub_self]

theorem thirteenSupport_finiteDimensional : FiniteDimensional (ZMod 19) thirteenSupport :=
  FiniteDimensional.of_injective thirteenCoordinate thirteenCoordinate_injective

theorem thirteenSupport_finrank_le_one : Module.finrank (ZMod 19) thirteenSupport ≤ 1 := by
  simpa only [Module.finrank_self] using
    thirteenCoordinate.finrank_le_finrank_of_injective thirteenCoordinate_injective

theorem classOf_mem_thirteenSupport (a : ℚˣ)
    (hval : ∀ (q : ℕ), q.Prime → q ≠ 13 → (19 : ℤ) ∣ padicValRat q (a : ℚ)) :
    Additive.ofMul (classOf a) ∈ thirteenSupport := by
  apply (mem_thirteenSupport _).mpr
  intro q hq h13
  rw [MazurTransfer.original_rational_nineteenth_power_valuation_formula_and_zero_detection.1]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hval q hq h13)

variable {W : Type} [AddCommGroup W] [Module (ZMod 19) W]



theorem dimension_le_one_of_injective_radicand_map
    (f : W →ₗ[ZMod 19] Additive PowerClasses) (hi : Function.Injective f)
    (hf : ∀ x : W, f x ∈ thirteenSupport) :
    FiniteDimensional (ZMod 19) W ∧ Module.finrank (ZMod 19) W ≤ 1 := by
  let g := restrictToThirteenSupport f hf
  have hg : Function.Injective g := by
    intro x y h
    exact hi (congrArg Subtype.val h)
  haveI := thirteenSupport_finiteDimensional
  have hW := FiniteDimensional.of_injective g hg
  exact ⟨hW, (g.finrank_le_finrank_of_injective hg).trans thirteenSupport_finrank_le_one⟩

end MazurTransfer.OriginalRationalThirteenSupportFiniteDimensionProof20261019

theorem solution : (∀ (x : Additive PowerClasses), x ∈ thirteenSupport ↔ ∀ (q : ℕ) (hq : q.Prime), q ≠ 13 → valuationLinearMap q hq x = 0) ∧ (Function.Injective thirteenCoordinate) ∧ (FiniteDimensional (ZMod 19) thirteenSupport) ∧ (Module.finrank (ZMod 19) thirteenSupport ≤ 1) ∧ (∀ (a : ℚˣ)
    (hval : ∀ (q : ℕ), q.Prime → q ≠ 13 → (19 : ℤ) ∣ padicValRat q (a : ℚ)), Additive.ofMul (classOf a) ∈ thirteenSupport) ∧ (∀ {W : Type} [AddCommGroup W] [Module (ZMod 19) W] (f : W →ₗ[ZMod 19] Additive PowerClasses) (hi : Function.Injective f)
    (hf : ∀ x : W, f x ∈ thirteenSupport), FiniteDimensional (ZMod 19) W ∧ Module.finrank (ZMod 19) W ≤ 1) := by
  exact ⟨MazurTransfer.OriginalRationalThirteenSupportFiniteDimensionProof20261019.mem_thirteenSupport, MazurTransfer.OriginalRationalThirteenSupportFiniteDimensionProof20261019.thirteenCoordinate_injective, MazurTransfer.OriginalRationalThirteenSupportFiniteDimensionProof20261019.thirteenSupport_finiteDimensional, MazurTransfer.OriginalRationalThirteenSupportFiniteDimensionProof20261019.thirteenSupport_finrank_le_one, MazurTransfer.OriginalRationalThirteenSupportFiniteDimensionProof20261019.classOf_mem_thirteenSupport, MazurTransfer.OriginalRationalThirteenSupportFiniteDimensionProof20261019.dimension_le_one_of_injective_radicand_map⟩
#print axioms solution
