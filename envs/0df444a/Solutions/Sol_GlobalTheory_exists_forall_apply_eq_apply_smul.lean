-- Prove2me | solution 1 for GlobalTheory.exists_forall_apply_eq_apply_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:46.224321+00:00
-- url     : https://prove2.me/submissions/fa0e45c2-e7e0-42e8-821f-772e299761e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_exists_apply_eq_apply_smul
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
    (h : ∀ a, (∀ g : G, g • a = a) → φ a = ψ a) : ∃ g : G, ∀ a, ψ a = φ (g • a) := by
  classical
  cases nonempty_fintype G
  by_contra! hcon
  choose a ha using hcon
  let n : G → ℕ := fun g ↦ Fintype.equivFin G g
  have hn : Function.Injective n := Fin.val_injective.comp (Fintype.equivFin G).injective
  obtain ⟨g, hg⟩ := exists_apply_eq_apply_smul (G := G) (Polynomial.mapRingHom φ)
    (Polynomial.mapRingHom ψ) (fun p hp ↦ by
      ext i
      simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      exact h _ fun g ↦ by rw [← Polynomial.coeff_smul, hp])
    (∑ g, Polynomial.monomial (n g) (a g))
  have := congrArg (fun p ↦ Polynomial.coeff p (n g)) hg
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_smul,
    Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hn.eq_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  exact ha g this
end GlobalTheory
