-- Prove2me | solution 1 for GlobalTheory.QuasiFiniteFibreFlat.flat_baseChange_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:22.121446+00:00
-- url     : https://prove2.me/submissions/489c9f33-200f-402f-96d6-4014ed1eda23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatOfQuasiFiniteOfFlatFibres
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.QuasiFiniteFibreFlat
namespace GlobalTheory.QuasiFiniteFibreFlat
theorem _root_.solution (S C T D : Type) [CommRing S] [CommRing C] [CommRing T] [CommRing D]
    [Algebra S C] [Algebra S T] [Algebra S D] [Algebra T D] [IsScalarTower S T D]
    [Module.Flat T D] [h : Module.Flat C (C ⊗[S] T)] : Module.Flat C (C ⊗[S] D) := by
  let l := IsScalarTower.toAlgHom S T D
  have hl : (l : T →+* D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h1 := (RingHom.flat_algebraMap_iff.mpr h).comp (RingHom.Flat.lTensor (S := S) C hl)
  rw [← RingHom.flat_algebraMap_iff]
  convert h1 using 1
  ext c
  simp
end GlobalTheory.QuasiFiniteFibreFlat
