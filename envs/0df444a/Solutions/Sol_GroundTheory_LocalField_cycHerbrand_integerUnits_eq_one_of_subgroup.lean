-- Prove2me | solution 1 for GroundTheory.LocalField.cycHerbrand_integerUnits_eq_one_of_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:05:08.44181+00:00
-- url     : https://prove2.me/submissions/d4d97fdf-d7e8-410e-8c01-0d72b8d92bee

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_eq_of_injective
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_eq_one_of_subsingleton


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
    (V : Subgroup 𝒪[L]ˣ) [V.FiniteIndex] [MulDistribMulAction (L ≃ₐ[K] L) V]
    (hV : ∀ (g : L ≃ₐ[K] L) (v : V), ((g • v : V) : 𝒪[L]ˣ) = g • (v : 𝒪[L]ˣ))
    [Subsingleton (TateZero (L ≃ₐ[K] L) V)] [Subsingleton (TateNegOne (L ≃ₐ[K] L) V)] :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  have : V.subtype.range.FiniteIndex := by rw [Subgroup.range_subtype]; infer_instance
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_injective V.subtype V.subtype_injective hV σ
  obtain ⟨h3, h4⟩ := cycHerbrand_eq_one_of_subsingleton (G := L ≃ₐ[K] L) (M := V) hσ
  exact ⟨h1.mp h3, h2.symm.trans h4⟩
end GroundTheory.LocalField
