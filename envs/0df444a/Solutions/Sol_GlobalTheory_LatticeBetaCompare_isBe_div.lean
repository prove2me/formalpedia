-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.isBe_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:20:59.486369+00:00
-- url     : https://prove2.me/submissions/b5da4da8-7395-45fa-a995-e2172ec6c61a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_GlobalTheory_LatticeBetaCompare_isBe_ne_zero
import Theorems.Thm_GlobalTheory_LatticeBetaCompare_reflexIdeal_mul
import Theorems.Thm_GlobalTheory_LatticeBetaCompare_exists_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
variable {Dw c}
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution {𝔞 𝔟 : Ideal (𝓞 E)} {α β : c.F} (h0 : 𝔞 ≠ ⊥) (h : IsBe Dw c 𝔞 α) (h' : IsBe Dw c (𝔞 * 𝔟) β) :
    IsBe Dw c 𝔟 (β / α) := by
  have hα := isBe_ne_zero h0 h
  obtain ⟨⟨a, rfl, ha⟩, h⟩ := h
  obtain ⟨⟨b, rfl, hb⟩, h'⟩ := h'
  rw [reflexIdeal_mul, ← ha] at hb
  refine ⟨exists_quotient hα hb, fun s => ?_⟩
  have : (Ideal.absNorm 𝔞 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h0)
  rw [map_div₀, norm_div, div_pow, h, h', map_mul, Nat.cast_mul, mul_pow,
    mul_div_cancel_left₀ _ (pow_ne_zero _ this)]
end GlobalTheory.LatticeBetaCompare
