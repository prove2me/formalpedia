-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.agree_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:42.271298+00:00
-- url     : https://prove2.me/submissions/6040cb84-e86e-4edf-9615-8ee5ceb3a586

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M : ℕ} {Λ Λ' Λ'' : Lt E n} (h : Agree M Λ Λ') (h' : Agree M Λ' Λ'') :
    Agree M Λ Λ'' := by
  obtain ⟨s, hs, hc, h1, h2⟩ := h
  obtain ⟨t, ht, hd, h3, h4⟩ := h'
  refine ⟨s * t, Nat.mul_pos hs ht, Nat.Coprime.mul_left hc hd, fun v hv => ?_, fun v hv => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]; exact h3 _ (h1 v hv)
  · rw [Nat.cast_mul, mul_smul]; exact h2 _ (h4 v hv)
end GlobalTheory.SW.Nbr
