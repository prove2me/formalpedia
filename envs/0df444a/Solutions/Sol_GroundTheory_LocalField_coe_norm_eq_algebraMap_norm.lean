-- Prove2me | solution 1 for GroundTheory.LocalField.coe_norm_eq_algebraMap_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:06.760527+00:00
-- url     : https://prove2.me/submissions/ec5bd81a-102b-49ae-b6bd-79105fccb3ee

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Theorems.Thm_GroundTheory_LocalField_algebraMap_norm_eq_prod_embeddings_of_splits
import Theorems.Thm_GroundTheory_LocalField_finiteDimensional_extendScalars
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
variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
include hK
namespace GroundTheory.LocalField
theorem _root_.solution [FiniteDimensional K F] [(L'.subgroupOf K').FiniteIndex]
    (a : fixedModule Ωˣ L') :
    (((norm Ωˣ K' L' a : fixedModule Ωˣ K') : Ωˣ) : Ω) =
      algebraMap E Ω (Algebra.norm E
        ((unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL) a :
          (extendScalars hEF)ˣ) : extendScalars hEF)) := by
  classical
  have := finiteDimensional_extendScalars hEF
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  let _ := Fintype.ofFinite (K' ⧸ L'.subgroupOf K')
  let _ : Fintype (extendScalars hEF →ₐ[E] Ω) := Fintype.ofFinite _
  have hsplit : ∀ x : extendScalars hEF, ((minpoly E x).map (algebraMap E Ω)).Splits := fun x => by
    rw [← minpoly.algebraMap_eq (algebraMap (extendScalars hEF) Ω).injective x]
    exact Normal.splits inferInstance _
  rw [algebraMap_norm_eq_prod_embeddings_of_splits E (extendScalars hEF) Ω hsplit, coe_norm,
    finprod_eq_prod_of_fintype, Units.coe_prod]
  refine Fintype.prod_equiv (cosetEmbeddingEquivRel K' L' hEF hK hL) _ _ fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H σ => rfl
end GroundTheory.LocalField
