-- Prove2me | solution 1 for GlobalTheory.SignedLengthOrdFracDet.relLength_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:30.972292+00:00
-- url     : https://prove2.me/submissions/e526c41f-e58f-4abb-b289-cbfb6f188631

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
import Theorems.Thm_GlobalTheory_relLength_map_mkQ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SignedLengthOrdFracDet
open Module Submodule
namespace GlobalTheory.SignedLengthOrdFracDet
theorem _root_.solution {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A D C : Submodule R V} (hD : D ≤ A) (hC : C ≤ D) :
    relLength A C = relLength A D + relLength D C := by
  rw [relLength_eq_length_map_mkQ A C, relLength_eq_length_map_mkQ D C,
    ← relLength_map_mkQ hC A, add_comm]
  have hle : D.map C.mkQ ≤ A.map C.mkQ := Submodule.map_mono hD
  rw [relLength_def, ← (Submodule.submoduleOfEquivOfLe hle).length_eq]
  exact Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.mkQ _)
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
end GlobalTheory.SignedLengthOrdFracDet
