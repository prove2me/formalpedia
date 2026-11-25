-- Prove2me | solution 1 for GroundTheory.LocalField.span_conjugates_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:37.061574+00:00
-- url     : https://prove2.me/submissions/a5d68ba4-7e99-419b-9a7f-0bca02bd29ec

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution {θ : L} (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) :
    Submodule.span K (Set.range fun σ : Gal(L/K) => σ θ) = ⊤ := by
  have := (basisOfLinearIndependentOfCardEqFinrank hθ
    (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L))).span_eq
  simpa [coe_basisOfLinearIndependentOfCardEqFinrank] using this
end GroundTheory.LocalField
