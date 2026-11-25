-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.comp_eq_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:04.822224+00:00
-- url     : https://prove2.me/submissions/41c8e0c1-a736-4bea-8d82-554a26343ca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_exists_forall_apply_eq_apply_smul
import Theorems.Thm_GlobalTheory_specAction_fromSpec
import Theorems.Thm_GlobalTheory_isPullback_fromSpec_app
import Theorems.Thm_GlobalTheory_pullbackAction_fst
import Theorems.Thm_GlobalTheory_pullbackAction_snd
import Theorems.Thm_GlobalTheory_exists_specMap_fromSpec_eq_of_mem
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


attribute [reassoc (attr := simp)] GlobalTheory.pullbackAction_fst
attribute [reassoc (attr := simp)] GlobalTheory.pullbackAction_snd

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open GlobalTheory.IsAffineQuotient
variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {ρ : G →* Aut X} {π : X ⟶ Y}
  (h : IsAffineQuotient ρ π) {k : Type u} [Field k]
include h
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution (x y : Spec (.of k) ⟶ X) :
    x ≫ π = y ≫ π ↔ ∃ g, x ≫ (ρ g).hom = y := by
  refine ⟨fun e ↦ ?_, by rintro ⟨g, rfl⟩; rw [Category.assoc, h.comp_eq]⟩
  have := h.isAffineHom
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((x ≫ π) default)) isOpen_univ
  have hW : IsAffineOpen W := hW
  have hV := hW.preimage π
  have hy : (y ≫ π) default ∈ W := e ▸ hx
  obtain ⟨φ, rfl⟩ := exists_specMap_fromSpec_eq_of_mem x hV hx
  obtain ⟨ψ, rfl⟩ := exists_specMap_fromSpec_eq_of_mem y hV hy
  rw [Category.assoc, Category.assoc, (isPullback_fromSpec_app π hW hV).w, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, cancel_mono, Spec.map_inj] at e
  let := sectionsAction ρ _ (h.preimage_le W)
  obtain ⟨g, hg⟩ := exists_forall_apply_eq_apply_smul (G := G) φ.hom ψ.hom fun a ha ↦ by
    let := (π.app W).hom.toAlgebra
    obtain ⟨b, rfl⟩ := (h.isInvariant W).2.2.isInvariant a ha
    exact congr($e b)
  refine ⟨g⁻¹, ?_⟩
  rw [Category.assoc, ← specAction_fromSpec ρ hV (h.preimage_le W), specAction_hom,
    ← Spec.map_comp_assoc, inv_inv]
  congr 2
  ext a
  exact (hg a).symm
end GlobalTheory.IsAffineQuotient
