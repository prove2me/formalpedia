-- Prove2me | solution 1 for GlobalTheory.SW.UnitaryLeft.unit_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:45:36.135629+00:00
-- url     : https://prove2.me/submissions/63c1aadc-577a-452a-b301-08eb0f2fde49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_emb_cc
import Theorems.Thm_GlobalTheory_SW_HAct_emb_cc


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UnitaryLeft
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.UnitaryLeft
theorem _root_.solution {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (τ : E →+* ℂ) :
    ((h.map τ).map conj)ᵀ * h.map τ = 1 := by
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map τ) hh
  simp only [Matrix.map_mul] at h1
  rw [Matrix.map_one _ (map_zero τ) (map_one τ)] at h1
  rw [← h1]
  congr 1
  ext i j
  simp [ccT, emb_cc]
end GlobalTheory.SW.UnitaryLeft
