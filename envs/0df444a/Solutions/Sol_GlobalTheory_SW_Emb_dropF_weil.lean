-- Prove2me | solution 1 for GlobalTheory.SW.Emb.dropF_weil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:30.507379+00:00
-- url     : https://prove2.me/submissions/2d364cd4-a98d-4a22-8444-ef72f4c737c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_emb_mem
import Theorems.Thm_GlobalTheory_SW_Emb_transH_drop
import Theorems.Thm_GlobalTheory_T_hermitianWeilAction_unitaryGroup_testFunctions
import Theorems.Thm_GlobalTheory_T_tendsto_thH_pushZ_atTop_thH_dropF


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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.Emb
theorem _root_.solution (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ} (hφ : IsSB φ) :
    dropF (weil Ψ (emb γ) φ) = weil Ψ γ (dropF φ) := by
  obtain ⟨hsb, htr, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n (N + 1) hn (emb γ) (emb_mem hγ) φ hφ
  have hd := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N φ hφ).1
  have hdw := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ hsb).1
  exact (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ (dropF φ) hd).2.2.1 _ hdw (transH_drop hΨ hγ hφ hsb htr)
end GlobalTheory.SW.Emb
