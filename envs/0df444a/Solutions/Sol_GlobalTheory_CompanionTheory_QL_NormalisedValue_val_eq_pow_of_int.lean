-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.val_eq_pow_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:00.711376+00:00
-- url     : https://prove2.me/submissions/8320e4f3-13b8-44b4-953e-d2a4a27103a5

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_irreducible_pi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
private theorem isUnit_iff_valuation_eq_one' (y : 𝒪[F]) : IsUnit y ↔ ValuativeRel.valuation F (y : F) = 1 := by
  first
    | exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one
    | simpa using (Valuation.integer.integers (ValuativeRel.valuation F)).isUnit_iff_valuation_eq_one (x := y)
end GlobalTheory.CompanionTheory.QL.NormalisedValue
end

set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
theorem _root_.solution (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0)
    (hxO : ValuativeRel.valuation F x ≤ 1) :
    ∃ n : ℕ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ n := by
  have hxI : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hxO
  have hx' : (⟨x, hxI⟩ : 𝒪[F]) ≠ 0 := by
    intro h0
    exact hx (congrArg Subtype.val h0)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' (irreducible_pi h)
  refine ⟨n, ?_⟩
  have hv := congrArg (fun y : 𝒪[F] => ValuativeRel.valuation F (y : F)) hu
  have hu1 : ValuativeRel.valuation F ((u : 𝒪[F]) : F) = 1 := (isUnit_iff_valuation_eq_one' _).1 u.isUnit
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu1, one_mul] at hv
  exact hv
end GlobalTheory.CompanionTheory.QL.NormalisedValue
