-- Prove2me | solution 1 for GroundTheory.LocalField.coe_norm_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:54:12.08417+00:00
-- url     : https://prove2.me/submissions/8f2a9bd9-7452-4c3f-af65-08d7e4eae7fe

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Theorems.Thm_GroundTheory_LocalField_algebraMap_norm_eq_prod_embeddings_of_splits
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Abstract IntermediateField
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
local notation "G" => Ω ≃ₐ[K] Ω
variable (L : IntermediateField K Ω)
variable [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution [(L.fixingSubgroup.subgroupOf ⊤).FiniteIndex]
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    (((norm Ωˣ ⊤ L.fixingSubgroup a : fixedModule Ωˣ (⊤ : Subgroup G)) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K ((fixedModuleUnitsEquiv L a : Lˣ) : L)) := by
  classical
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  let _ := Fintype.ofFinite ((⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤)
  let _ : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
  have hsplit : ∀ x : L, ((minpoly K x).map (algebraMap K Ω)).Splits := fun x => by
    rw [← minpoly.algebraMap_eq (algebraMap L Ω).injective x]
    exact Normal.splits inferInstance _
  rw [algebraMap_norm_eq_prod_embeddings_of_splits K L Ω hsplit, coe_norm,
    finprod_eq_prod_of_fintype, Units.coe_prod]
  refine Fintype.prod_equiv (cosetEmbeddingEquiv L) _ _ fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H σ => rfl
end GroundTheory.LocalField
