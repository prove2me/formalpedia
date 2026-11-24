-- Prove2me | solution 1 for GlobalTheory.exists_apply_eq_apply_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:08.443802+00:00
-- url     : https://prove2.me/submissions/da92cc6a-2055-4d52-b718-18d02cec2ea8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type*} [Group G] [Finite G] {A k : Type*} [CommRing A] [MulSemiringAction G A]
  [CommRing k] [IsDomain k]
namespace GlobalTheory
theorem _root_.solution (φ ψ : A →+* k)
    (h : ∀ a, (∀ g : G, g • a = a) → φ a = ψ a) (a : A) : ∃ g : G, ψ a = φ (g • a) := by
  cases nonempty_fintype G
  have e : (MulSemiringAction.charpoly G a).map φ = (MulSemiringAction.charpoly G a).map ψ := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact h _ fun g ↦ MulSemiringAction.smul_coeff_charpoly a n g
  have e' : ((MulSemiringAction.charpoly G a).map φ).eval (ψ a) = 0 := by
    rw [e, Polynomial.eval_map, Polynomial.eval₂_at_apply, MulSemiringAction.eval_charpoly,
      map_zero]
  simpa [MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff, sub_eq_zero] using e'
end GlobalTheory
