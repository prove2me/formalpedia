-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.finsum_prod_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:19.977562+00:00
-- url     : https://prove2.me/submissions/ae6e649a-6563-40d0-9ac4-1f9f03666b7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
namespace GlobalTheory.SW.LinChange
theorem _root_.solution {A B : Type} [Finite B] [Nonempty B] (g : A → ℂ) :
    ∑ᶠ p : A × B, g p.1 = (Nat.card B : ℂ) * ∑ᶠ a, g a := by
  classical
  by_cases h : (Function.support g).Finite
  · have h2 : (Function.support fun p : A × B => g p.1).Finite :=
      (h.prod (Set.finite_univ (α := B))).subset fun p hp => ⟨hp, trivial⟩
    rw [finsum_curry _ h2, mul_finsum]
    refine finsum_congr fun a => ?_
    have := Fintype.ofFinite B
    simp [finsum_eq_sum_of_fintype]
  · have h2 : ¬ (Function.support fun p : A × B => g p.1).Finite := fun h2 =>
      h ((h2.image Prod.fst).subset fun a ha => ⟨(a, Classical.arbitrary B), ha, rfl⟩)
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h2, mul_zero]
end GlobalTheory.SW.LinChange
