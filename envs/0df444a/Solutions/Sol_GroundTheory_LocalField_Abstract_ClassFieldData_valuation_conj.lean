-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.valuation_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:06.971429+00:00
-- url     : https://prove2.me/submissions/ca372387-0a1a-45a0-92f1-10f24155ed5c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_eq_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_congr
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] {D : ClassFieldData G A}
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (σ : G) {K K' : OpenSubgroup G}
    (hK' : (K' : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom)
    (a : fixedModule A (K : Subgroup G)) (b : fixedModule A (K' : Subgroup G))
    (hb : (b : A) = σ • (a : A)) : D.valuation K' b = D.valuation K a := by
  have hf : inertiaDegree D.deg (K' : Subgroup G) = inertiaDegree D.deg (K : Subgroup G) := by
    rw [hK', inertiaDegree_map_conj]
  rw [valuation_eq_iff, hf, valuation_pow D K a]
  congr 1
  apply Subtype.ext
  have htop : (⊤ : Subgroup G).map (MulAut.conj σ).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj σ).surjective
  have : (((K : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((⊤ : Subgroup G).map (MulAut.conj σ).toMonoidHom)).FiniteIndex := by
    rw [← hK', htop]
    infer_instance
  have h1 := smul_norm σ (K := ⊤) a
  rw [(norm A ⊤ (K : Subgroup G) a).2 σ (Subgroup.mem_top σ), coe_norm_congr htop hK'.symm] at h1
  rw [h1]
  exact congrArg (fun x => (norm A ⊤ (K' : Subgroup G) x : A)) (Subtype.ext hb)
end GroundTheory.LocalField.Abstract.ClassFieldData
