-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.norm_one_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:59:02.904091+00:00
-- url     : https://prove2.me/submissions/0f8548c2-aa68-407d-af82-333e6eb17749

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUniformizerIdempotentFrameProd

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
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₂) :
    Algebra.norm F ((1, x) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (1, x) = (Algebra.lmul F R₁ 1).prodMap (Algebra.lmul F R₂ x) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₁), map_one LinearMap.det, one_mul]
end GlobalTheory.UnitLemma.Desc
