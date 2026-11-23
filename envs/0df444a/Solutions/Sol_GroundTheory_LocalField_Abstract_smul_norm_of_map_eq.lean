-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.smul_norm_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:54.548803+00:00
-- url     : https://prove2.me/submissions/978db1e1-893e-42d3-b115-8cab09ed88cb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_congr
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule
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
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K L : Subgroup G} (g : G) (hK : K.map (MulAut.conj g).toMonoidHom = K)
    (hL : L.map (MulAut.conj g).toMonoidHom = L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) :
    g • (norm A K L a : A) = norm A K L ⟨g • (a : A), by
      have := smul_mem_fixedModule a.2 g
      rwa [hL] at this⟩ := by
  have : ((L.map (MulAut.conj g).toMonoidHom).subgroupOf
      (K.map (MulAut.conj g).toMonoidHom)).FiniteIndex := by
    rw [hK, hL]
    infer_instance
  rw [smul_norm g a, coe_norm_congr hK hL]
end GroundTheory.LocalField.Abstract
