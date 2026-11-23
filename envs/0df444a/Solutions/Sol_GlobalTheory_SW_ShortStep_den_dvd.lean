-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.den_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:55.625949+00:00
-- url     : https://prove2.me/submissions/a7dca7dc-13bb-4693-962c-86a20e5e4ee3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_RowExt_intM_nat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
omit [IsCMField E]
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {α β : Type} {a b : ℕ} {A : Matrix α β E} (hA : Den a A) (h : a ∣ b) :
    Den b A := by
  obtain ⟨c, rfl⟩ := h
  have := RowExt.intM_nat c hA
  rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
end GlobalTheory.SW.ShortStep
