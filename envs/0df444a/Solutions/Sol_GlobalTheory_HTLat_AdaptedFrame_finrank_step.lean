-- Prove2me | solution 1 for GlobalTheory.HTLat.AdaptedFrame.finrank_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:47:27.955953+00:00
-- url     : https://prove2.me/submissions/97100400-b984-40a2-a3fd-cd77c5381bfa

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
namespace AdaptedFrame
theorem _root_.solution {W U₁ : Submodule C U} {j : ℕ} (F : AdaptedFrame W U₁ N j)
    {i : ℕ} (hi : i ≤ N) : Module.finrank C (step C F.f i) = i := by
  have h1 : F.f '' {k | (k : ℕ) < i} = Set.range (F.f ∘ Fin.castLE hi) := by
    rw [Set.range_comp, Fin.range_castLE]
  rw [step, h1, finrank_span_eq_card (F.indep.comp _ (Fin.castLE_injective hi)), Fintype.card_fin]
end AdaptedFrame
end GlobalTheory.HTLat
