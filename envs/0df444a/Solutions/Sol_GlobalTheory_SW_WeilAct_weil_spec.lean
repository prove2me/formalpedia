-- Prove2me | solution 1 for GlobalTheory.SW.WeilAct.weil_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:52.488744+00:00
-- url     : https://prove2.me/submissions/3b98448f-2cf0-4649-a2a0-91017bd57e81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Theorems.Thm_GlobalTheory_SW_WeilAct_exists_op

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
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.WeilAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.WeilAct
theorem _root_.solution (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) :
    IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) := by
  obtain ⟨W, hW⟩ := exists_op hΨ hn hγ
  have h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ := ⟨W φ, (hW φ hφ).1, (hW φ hφ).2.1⟩
  rw [weil, dif_pos h]
  exact h.choose_spec
end GlobalTheory.SW.WeilAct
