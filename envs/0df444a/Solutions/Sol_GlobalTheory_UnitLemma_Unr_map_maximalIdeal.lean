-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:22:19.66119+00:00
-- url     : https://prove2.me/submissions/b748eaa1-0adf-4d2e-a515-df0f34ab481c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intMap_spec
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_irreducible
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_irreducible_of_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (hU : IsUnrExt K K' d φ) :
    Ideal.map (intMap hU) (IsLocalRing.maximalIdeal K.O) = IsLocalRing.maximalIdeal K'.O := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have h1 := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have h2 : Irreducible (intMap hU ϖ) :=
    irreducible_of_val_one K' (by rw [intMap_spec, hU.2.2.1, val_irreducible K hϖ])
  rw [h1, Ideal.map_span, Set.image_singleton,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 h2]
end GlobalTheory.UnitLemma.Unr
