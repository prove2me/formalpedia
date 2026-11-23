-- Prove2me | solution 1 for GlobalTheory.QuotientCardinality.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:35.111208+00:00
-- url     : https://prove2.me/submissions/a5d9d136-a1c2-4a10-b36e-150cbcc7793b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.QuotientCardinality
open ValuativeRel
namespace GlobalTheory.QuotientCardinality
theorem _root_.solution : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ {a : ℤ} {m : ℕ} {u v : (↥(Valuation.integer (ValuativeRel.valuation F)))ˣ}, (↑ϖ : F) ^ a * (↑(↑u : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) * (↑(↑v : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) = (↑ϖ : F) ^ m → a = (↑m : ℤ) := by
  intro F _ _ _ _ ϖ hϖ a m u v h
  have hint := Valuation.integer.integers (ValuativeRel.valuation F)
  have hu : ValuativeRel.valuation F ((u : (ValuativeRel.valuation F).integer) : F) = 1 :=
    hint.one_of_isUnit u.isUnit
  have hv : ValuativeRel.valuation F ((v : (ValuativeRel.valuation F).integer) : F) = 1 :=
    hint.one_of_isUnit v.isUnit
  have hne : (ϖ : F) ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (Subtype.ext (by simpa using h0))
  have hpos : 0 < ValuativeRel.valuation F (ϖ : F) := by
    rw [pos_iff_ne_zero]
    exact (map_ne_zero (ValuativeRel.valuation F)).mpr hne
  have hne1 : ValuativeRel.valuation F (ϖ : F) ≠ 1 := by
    intro h1
    exact hϖ.not_isUnit ((hint.isUnit_iff_valuation_eq_one (x := ϖ)).mpr h1)
  have h2 := congrArg (ValuativeRel.valuation F) h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one, map_zpow₀, map_pow, ← zpow_natCast] at h2
  exact zpow_right_injective₀ hpos hne1 h2
end GlobalTheory.QuotientCardinality
