-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.isBe_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:05:52.434804+00:00
-- url     : https://prove2.me/submissions/ff78b22a-f7c8-4fba-b536-2f64f1535ffc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_GlobalTheory_LatticeBetaCompare_reflexIdeal_mul

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
theorem _root_.solution {𝔞 𝔟 : Ideal (𝓞 E)} {α β : c.F} (h : IsBe Dw c 𝔞 α) (h' : IsBe Dw c 𝔟 β) :
    IsBe Dw c (𝔞 * 𝔟) (α * β) := by
  obtain ⟨⟨a, rfl, ha⟩, h⟩ := h
  obtain ⟨⟨b, rfl, hb⟩, h'⟩ := h'
  refine ⟨⟨a * b, rfl, ?_⟩, fun s => ?_⟩
  · rw [reflexIdeal_mul, ← ha, ← hb, Ideal.span_singleton_mul_span_singleton]
  · rw [map_mul, norm_mul, mul_pow, h, h', map_mul, Nat.cast_mul, mul_pow]
end GlobalTheory.LatticeBetaCompare
