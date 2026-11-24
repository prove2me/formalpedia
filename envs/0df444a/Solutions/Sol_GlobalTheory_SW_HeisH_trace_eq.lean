-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:18.399815+00:00
-- url     : https://prove2.me/submissions/4d9794bc-1710-41aa-83b0-9f79ef06db70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Theorems.Thm_GlobalTheory_SW_Dict_sum_type


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.HeisH
theorem _root_.solution (hΨ : IsType Ψ) (t : E) :
    ((Algebra.trace ℚ E t : ℚ) : ℂ) = ∑ τ : Ψ, (τ.1 t + conj (τ.1 t)) := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := t)
  rw [eq_ratCast] at h
  rw [h, ← Equiv.sum_comp (RingHom.equivRatAlgHom (R := E) (S := ℂ))]
  exact Dict.sum_type hΨ fun σ => σ t
end GlobalTheory.SW.HeisH
