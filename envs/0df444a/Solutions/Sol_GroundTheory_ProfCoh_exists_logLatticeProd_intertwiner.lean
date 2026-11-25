-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_logLatticeProd_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:39.865993+00:00
-- url     : https://prove2.me/submissions/a76c6093-8f29-4bdc-875c-5c3c92c8d145

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
import Theorems.Thm_GroundTheory_ProfCoh_exists_logLatticeProd_real_equiv
import Theorems.Thm_GroundTheory_Global_exists_injective_intertwiner_of_real_equiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution :
    ∃ φ : logLattice L × ℤ →ₗ[ℤ] (InfinitePlace L → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ (g : L ≃ₐ[K] L) x, φ (((logLatticeRep K L).prod
          (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g x) =
        funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g (φ x) := by
  obtain ⟨e, he⟩ := exists_logLatticeProd_real_equiv (K := K) (L := L)
  exact exists_injective_intertwiner_of_real_equiv _ _ e he
end GroundTheory.ProfCoh
