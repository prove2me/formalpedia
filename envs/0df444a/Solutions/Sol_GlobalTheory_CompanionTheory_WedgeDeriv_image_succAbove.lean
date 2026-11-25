-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeDeriv.image_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:29.983596+00:00
-- url     : https://prove2.me/submissions/8b45563e-b7e0-4a43-96ef-e7e523235cfc

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
theorem _root_.solution {m n : ℕ} (f : Fin (m + 1) → Fin n) (hf : StrictMono f) (i : Fin (m + 1)) :
    univ.image (f ∘ i.succAbove) = (univ.image f).erase (f i) := by
  ext x
  simp only [mem_erase, mem_image, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne _ _ (hf.injective h), _, rfl⟩
  · rintro ⟨h, j, rfl⟩
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (fun e => h (by rw [e]))
    exact ⟨l, rfl⟩
end GlobalTheory.CompanionTheory.WedgeDeriv
