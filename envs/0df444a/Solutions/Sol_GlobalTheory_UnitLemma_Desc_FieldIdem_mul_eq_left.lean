-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.FieldIdem.mul_eq_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:51:43.146804+00:00
-- url     : https://prove2.me/submissions/413397f6-d5e7-4437-8d38-7b5f47f1233c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open Classical
variable {R : Type} [CommRing R]
namespace GlobalTheory.UnitLemma.Desc
namespace FieldIdem
theorem _root_.solution {u v : R} (hu : FieldIdem u) (hv : IsIdempotentElem v) (h : u * v ≠ 0) :
    u * v = u := by
  obtain ⟨z, hz⟩ := hu.2.2 v h
  calc u * v = (u * v * z) * v := by rw [hz]
    _ = u * v * z * v := rfl
    _ = u * (v * v) * z := by ring
    _ = u := by rw [hv.eq, hz]
end FieldIdem
end GlobalTheory.UnitLemma.Desc
