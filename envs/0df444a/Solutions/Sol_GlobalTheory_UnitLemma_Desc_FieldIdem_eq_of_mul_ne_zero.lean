-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.FieldIdem.eq_of_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:11.377843+00:00
-- url     : https://prove2.me/submissions/44e1fa10-1623-435e-87b7-8b9a1bfc2283

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_FieldIdem_mul_eq_left

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
theorem _root_.solution {u v : R} (hu : FieldIdem u) (hv : FieldIdem v) (h : u * v ≠ 0) :
    u = v := by
  have h1 : u * v = u := hu.mul_eq_left hv.1 h
  have h2 : v * u = v := hv.mul_eq_left hu.1 (by rwa [mul_comm])
  calc u = u * v := h1.symm
    _ = v * u := mul_comm _ _
    _ = v := h2
end FieldIdem
end GlobalTheory.UnitLemma.Desc
