-- Prove2me | solution 1 for GlobalTheory.HTLat.map_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:25.18489+00:00
-- url     : https://prove2.me/submissions/416d79bb-01f0-444a-a2ea-1c172bae1b33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
namespace GlobalTheory.HTLat
theorem _root_.solution {U' : Type} [AddCommGroup U'] [Module C U'] (g : U →ₗ[C] U') (f : Fin N → U) (i : ℕ) :
    (step C f i).map g = step C (g ∘ f) i := by
  rw [step, step, Submodule.map_span, Set.image_comp]
end GlobalTheory.HTLat
