-- Prove2me | solution 1 for GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:18.823021+00:00
-- url     : https://prove2.me/submissions/d4c4577b-fbdd-41f9-8dbb-8eea64e16186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatComapMapOfOneTmulMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatComapMapOfOneTmulMemStatement
import Theorems.Thm_GlobalTheory_flat_comap_map_of_one_tmul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {B C R : Type} [CommRing B] [CommRing C] [CommRing R] [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R), (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) → r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by
  first | exact @GlobalTheory.flat_comap_map_of_one_tmul_mem | exact GlobalTheory.flat_comap_map_of_one_tmul_mem | (intros; apply GlobalTheory.flat_comap_map_of_one_tmul_mem <;> assumption)
end _root_.GlobalTheory.T
