-- Prove2me | solution 1 for GroundTheory.LocalField.cycHerbrand_units_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:30.274492+00:00
-- url     : https://prove2.me/submissions/3e43fd6f-c6d1-4db5-b1bc-b483fd99799c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_unitsOrd_surjective
import Theorems.Thm_GroundTheory_LocalField_exact_unitsIncl_unitsOrd
import Theorems.Thm_GroundTheory_LocalField_unitsOrd_cycSubOne
import Theorems.Thm_GroundTheory_LocalField_unitsOrd_cycNorm
import Theorems.Thm_GroundTheory_Global_cycNorm_cycSubOne
import Theorems.Thm_GroundTheory_Global_cycSubOne_cycNorm
import Theorems.Thm_GroundTheory_Global_cyclicHerbrand_trivial_int
import Theorems.Thm_GroundTheory_Global_hasCyclicHerbrand_of_finite
import Theorems.Thm_GroundTheory_GroupCoh_HasHerbrandQuotient_of_shortExact_left_right
import Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_mul_of_shortExact
import Theorems.Thm_GroundTheory_LocalField_toAdditive_cycNorm
import Theorems.Thm_GroundTheory_LocalField_toAdditive_cycSubOne
import Theorems.Thm_GroundTheory_LocalField_unitsIncl_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {σ : L ≃ₐ[K] L}
namespace GroundTheory.LocalField
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (hA : HasHerbrandQuotient
      (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
      (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ))) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ *
          Fintype.card (L ≃ₐ[K] L) := by
  have hi : Function.Injective (MonoidHom.toAdditive (unitsIncl L)) := unitsIncl_injective
  have hC : HasHerbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) :=
    hasCyclicHerbrand_of_finite (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) hσ
  have hCv : herbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) = Fintype.card (L ≃ₐ[K] L) :=
    cyclicHerbrand_trivial_int σ
  refine ⟨HasHerbrandQuotient.of_shortExact_left_right hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, ?_⟩
  rw [cycHerbrand, herbrandQuotient_eq_mul_of_shortExact hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, hCv]
  rfl
end GroundTheory.LocalField
