-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeDeriv.card_filter_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:11.376087+00:00
-- url     : https://prove2.me/submissions/004a1955-ff63-4ab2-850b-806d85dbb400

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeDeriv
namespace GlobalTheory.CompanionTheory.WedgeDeriv
theorem _root_.solution {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (i : Fin m) :
    (((univ.image f).erase (f i)).filter fun c => c < f i).card = i := by
  have : (((univ.image f).erase (f i)).filter fun c => c < f i) = (Iio i).image f := by
    ext x
    simp only [mem_filter, mem_erase, mem_image, mem_univ, true_and, mem_Iio]
    constructor
    · rintro ⟨⟨_, j, rfl⟩, h⟩
      exact ⟨j, hf.lt_iff_lt.1 h, rfl⟩
    · rintro ⟨j, h, rfl⟩
      exact ⟨⟨(hf h).ne, j, rfl⟩, hf h⟩
  rw [this, card_image_of_injective _ hf.injective, Fin.card_Iio]
end GlobalTheory.CompanionTheory.WedgeDeriv
