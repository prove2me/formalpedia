-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeDeriv.det_one_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:19.113941+00:00
-- url     : https://prove2.me/submissions/0f26395e-53f7-4eb6-8415-c3a472f17e4a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


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
theorem _root_.solution {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g).det = if univ.image f = univ.image g then 1 else 0 := by
  split_ifs with h
  · have : f = g := by
      refine (hf.range_inj hg).1 ?_
      have := congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) h
      simpa using this
    subst this
    rw [submatrix_one _ hf.injective, det_one]
  · have : ∃ i, f i ∉ univ.image g := by
      by_contra hc
      push Not at hc
      apply h
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, _, rfl⟩ := mem_image.1 hx
        exact hc i
      · rw [card_image_of_injective _ hf.injective, card_image_of_injective _ hg.injective]
    obtain ⟨i, hi⟩ := this
    refine det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [submatrix_apply, one_apply_ne]
    intro he
    exact hi (mem_image.2 ⟨j, mem_univ _, he.symm⟩)
end GlobalTheory.CompanionTheory.WedgeDeriv
