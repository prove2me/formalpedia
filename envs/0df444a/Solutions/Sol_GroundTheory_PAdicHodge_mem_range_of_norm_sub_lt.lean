-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_range_of_norm_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:03.34318+00:00
-- url     : https://prove2.me/submissions/07e10761-593e-4a21-a5de-cfd0cb2e7833

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [NormedField E] [NormedAlgebra F E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsAlgClosed E] {α : E} (b : F) (hα : IsSeparable F α)
    (h : ∀ α' : E, IsConjRoot F α α' → α ≠ α' → ‖α - algebraMap F E b‖ < ‖α - α'‖) :
    α ∈ Set.range (algebraMap F E) := by
  have hαi : IsIntegral F α := hα.isIntegral
  let L := algebraicClosure F E
  let x : L := ⟨α, hαi⟩
  have : IsKrasner F L := IsKrasner.of_completeSpace F L
  have hxsep : (minpoly F x).Separable := by
    rw [IntermediateField.minpoly_eq]; exact hα
  have sp : ((minpoly F x).map (algebraMap F L)).Splits := by
    rw [IntermediateField.minpoly_eq]
    refine IntermediateField.splits_of_splits (IsAlgClosed.splits _) fun z hz => ?_
    rw [mem_rootSet] at hz
    exact ⟨minpoly F α, minpoly.monic hαi, by rw [← aeval_def]; exact hz.2⟩
  have key := IsKrasner.krasner hxsep sp (isIntegral_algebraMap (x := b)) fun x' hx' hne => by
    have hc : IsConjRoot F α (x' : E) := by
      unfold IsConjRoot at hx' ⊢
      rwa [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq] at hx'
    have hne' : α ≠ (x' : E) := fun e => hne (Subtype.ext e)
    exact h x' hc hne'
  rw [IntermediateField.adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ _)] at key
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 key
  exact ⟨c, congrArg Subtype.val hc⟩
end GroundTheory.PAdicHodge
