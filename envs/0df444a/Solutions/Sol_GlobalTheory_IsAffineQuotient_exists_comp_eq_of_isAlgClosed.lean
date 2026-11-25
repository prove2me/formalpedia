-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.exists_comp_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:09.613826+00:00
-- url     : https://prove2.me/submissions/d72fee14-c5c9-4f66-8272-ae99bf25a003

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_exists_ringHom_extension_of_isIntegral
import Theorems.Thm_GlobalTheory_isPullback_fromSpec_app
import Theorems.Thm_GlobalTheory_exists_specMap_fromSpec_eq_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open GlobalTheory.IsAffineQuotient
variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {ρ : G →* Aut X} {π : X ⟶ Y}
  (h : IsAffineQuotient ρ π) {k : Type u} [Field k]
include h
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution [IsAlgClosed k] (y : Spec (.of k) ⟶ Y) :
    ∃ x : Spec (.of k) ⟶ X, x ≫ π = y := by
  have := h.isIntegralHom
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (y default)) isOpen_univ
  have hW : IsAffineOpen W := hW
  have hV := hW.preimage π
  obtain ⟨φ, rfl⟩ := exists_specMap_fromSpec_eq_of_mem y hW hy
  let := (π.app W).hom.toAlgebra
  have := (h.isInvariant W).2.1
  have : Algebra.IsIntegral Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := ⟨π.isIntegral_app W hW⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extension_of_isIntegral (A := Γ(X, π ⁻¹ᵁ W)) φ.hom
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, (isPullback_fromSpec_app π hW hV).w, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext hψ
end GlobalTheory.IsAffineQuotient
