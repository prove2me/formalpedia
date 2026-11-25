-- Prove2me | solution 1 for GlobalTheory.HostModel.coeff_F_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:49:22.326237+00:00
-- url     : https://prove2.me/submissions/3a9c9650-9178-4060-9225-1e2058386080

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Theorems.Thm_GlobalTheory_HostModel_coeff_F

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.HostModel
theorem _root_.solution (l : Level H) (F : IntermediateField ℚ ℂ) :
    (coeff l).F ≤ F ↔ zeta l.M' ∈ F ∧ ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F := by
  constructor
  · exact fun h => ⟨h (coeff l).zeta_mem, fun τ a => h ((coeff l).conj τ a)⟩
  · rintro ⟨hz, hc⟩
    rw [coeff_F, sup_le_iff, normalClosure_le_iff, IntermediateField.adjoin_simple_le_iff]
    refine ⟨fun f => ?_, hz⟩
    rintro _ ⟨a, rfl⟩
    exact hc f.toRingHom a
end GlobalTheory.HostModel
