-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.nrm_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:52:04.658239+00:00
-- url     : https://prove2.me/submissions/98a5a387-b135-4c93-b297-b8c2562499e5

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_mem_iff_val_le
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_one_lt_q
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_val_eq_pow_of_int
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_nrm_eq_zpow
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
private theorem nrm_le_one_of_valuation_le_one (h : LF O ϖ nrm q) (x : F) (hx : ValuativeRel.valuation F x ≤ 1) :
    nrm x ≤ 1 := by
  by_cases h0 : x = 0
  · simp [h0]
  · obtain ⟨n, hn⟩ := val_eq_pow_of_int h h0 hx
    rw [nrm_eq_zpow h (e := (n : ℤ)) (by rw [hn, _root_.zpow_natCast]), _root_.zpow_neg, _root_.zpow_natCast]
    have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (one_lt_q h).le
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hq)
private theorem nrm_le_inv_q_of_valuation_lt_one (h : LF O ϖ nrm q) (x : F) (hx : ValuativeRel.valuation F x < 1) :
    nrm x ≤ (q : ℝ)⁻¹ := by
  obtain ⟨o, hoO, rfl⟩ := (h.lt_one x).1 hx
  rw [map_mul, h.nrm_pi]
  have ho : nrm o ≤ 1 := nrm_le_one_of_valuation_le_one h o ((mem_iff_val_le h o).1 hoO)
  have hq : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  calc (q : ℝ)⁻¹ * nrm o ≤ (q : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left ho hq
    _ = (q : ℝ)⁻¹ := mul_one _
end GlobalTheory.CompanionTheory.QL.NormalisedValue
end

set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
theorem _root_.solution (h : LF O ϖ nrm q) (x : F) :
    nrm x ≤ 1 ↔ ValuativeRel.valuation F x ≤ 1 := by
  constructor
  · intro hn
    by_contra hv
    have hlt : 1 < ValuativeRel.valuation F x := lt_of_not_ge hv
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hlt
    have hi : ValuativeRel.valuation F x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx).1 hlt
    have h2 : nrm x⁻¹ ≤ (q : ℝ)⁻¹ := nrm_le_inv_q_of_valuation_lt_one h _ hi
    have hq : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_q h)
    rw [map_inv₀] at h2
    have hpos : 0 < nrm x := nrm.pos hx
    have h3 : (nrm x)⁻¹ < 1 := lt_of_le_of_lt h2 hq
    have h4 : 1 < nrm x := (inv_lt_one₀ hpos).1 h3
    linarith
  · exact nrm_le_one_of_valuation_le_one h x
end GlobalTheory.CompanionTheory.QL.NormalisedValue
