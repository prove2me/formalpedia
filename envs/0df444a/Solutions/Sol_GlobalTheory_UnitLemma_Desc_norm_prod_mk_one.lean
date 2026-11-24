-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.norm_prod_mk_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:59:03.738409+00:00
-- url     : https://prove2.me/submissions/41979912-c323-4b3f-8843-472ec4b9ab33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartProdInl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {K : UQ} (B₁ B₂ : InvAlg K) (y : B₁.A) :
    Algebra.norm K.E ((y, 1) : B₁.A × B₂.A) = Algebra.norm K.E y := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul K.E (B₁.A × B₂.A) (y, 1) =
      LinearMap.prodMap (Algebra.lmul K.E B₁.A y) (Algebra.lmul K.E B₂.A 1) := by
    ext z <;> simp
  rw [h, LinearMap.det_prodMap, map_one, map_one, mul_one]
end GlobalTheory.UnitLemma.Desc
