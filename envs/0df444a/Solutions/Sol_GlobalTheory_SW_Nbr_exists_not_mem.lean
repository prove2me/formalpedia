-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.exists_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:57.677765+00:00
-- url     : https://prove2.me/submissions/0baae19e-1c5f-4cd8-995c-c60a3c6ff9cd

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
theorem _root_.solution {Q : Ideal (𝓞 E)} (hQ : Q ≠ ⊥) {t : E} (ht : ¬ IsIntegral ℤ t)
    (h : ∀ d ∈ Q, IsIntegral ℤ ((d : E) * t)) : ∃ d ∈ Q, ∃ r ∉ Q, ((r : 𝓞 E) : E) = (d : E) * t := by
  by_contra hn
  push Not at hn
  refine ht (isIntegral_trans (A := 𝓞 E) t ?_)
  refine isIntegral_of_smul_mem_submodule (Submodule.map (Algebra.linearMap (𝓞 E) E) Q) ?_
    (Submodule.FG.map _ (IsNoetherian.noetherian _)) t ?_
  · obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
    rw [Submodule.ne_bot_iff]
    exact ⟨_, ⟨c, hc, rfl⟩, fun h0 => hc0 (RingOfIntegers.ext h0)⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact ⟨⟨_, h d hd⟩, by_contra fun h0 => hn d hd _ h0 rfl, mul_comm _ _⟩
end GlobalTheory.SW.Nbr
