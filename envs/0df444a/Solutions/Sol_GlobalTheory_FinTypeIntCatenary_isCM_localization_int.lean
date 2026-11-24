-- Prove2me | solution 1 for GlobalTheory.FinTypeIntCatenary.isCM_localization_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:50.963724+00:00
-- url     : https://prove2.me/submissions/9abba3f7-0402-4bc0-8dbe-ed5f920926ab

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinTypeIntCatenary
open ReciprocityTheory.CA
namespace GlobalTheory.FinTypeIntCatenary
theorem _root_.solution (p : Ideal ℤ) [p.IsMaximal] :
    IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = 1 := by
  have hp : p ≠ ⊥ := by
    intro h
    have : (⊥ : Ideal ℤ).IsMaximal := h ▸ inferInstance
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr this)
  haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hp _
  have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
  refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, hd⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
  refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact IsSMulRegular.of_ne_zero hϖ.ne_zero
end GlobalTheory.FinTypeIntCatenary
