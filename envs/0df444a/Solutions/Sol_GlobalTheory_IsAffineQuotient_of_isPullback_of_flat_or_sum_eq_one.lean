-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.of_isPullback_of_flat_or_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:24.733554+00:00
-- url     : https://prove2.me/submissions/109d4799-0989-40d8-90fc-f287c1212fb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_isInvariant_of_isBaseChange_of_sum_eq_one
import Theorems.Thm_GlobalTheory_IsAffineQuotient_of_cover
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_faithfulSMul_of_isBaseChange
import Theorems.Thm_GlobalTheory_isInvariant_of_isBaseChange
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
variable {G : Type v} [Group G] {X Y X' Y' S S' : Scheme.{u}}
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
open GlobalTheory.IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y} (h : IsAffineQuotient ρ π)
  {ρ' : G →* Aut X'} {π' : X' ⟶ Y'} {p : X' ⟶ X} {t : Y' ⟶ Y} (H : IsPullback p π' π t)
  (hp : ∀ g, (ρ' g).hom ≫ p = p ≫ (ρ g).hom) (hπ' : ∀ g, (ρ' g).hom ≫ π' = π')
include h H hp hπ'
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution [Fintype G]
    (hW : ∀ (W : Y.Opens) (_ : IsAffineOpen W) (W' : Y'.Opens) (_ : IsAffineOpen W')
      (e : W' ≤ t ⁻¹ᵁ W), (t.appLE W W' e).hom.Flat ∨
        letI := sectionsAction ρ _ (h.preimage_le W)
        ∃ c : Γ(X, π ⁻¹ᵁ W), ∑ g : G, g • c = 1) :
    IsAffineQuotient ρ' π' := by
  have := h.isAffineHom
  have : IsAffineHom π' := MorphismProperty.of_isPullback H ‹_›
  refine of_cover hπ' fun y ↦ ?_
  obtain ⟨_, ⟨W, hW₁, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t y)) isOpen_univ
  obtain ⟨_, ⟨W', hW₂, rfl⟩, hy', e⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ t ⁻¹ᵁ W from hy) (t ⁻¹ᵁ W).isOpen
  have hW₁ : IsAffineOpen W := hW₁
  have hW₂ : IsAffineOpen W' := hW₂
  have e : W' ≤ t ⁻¹ᵁ W := e
  have e' : π' ⁻¹ᵁ W' ≤ p ⁻¹ᵁ π ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, H.w]
    exact π'.preimage_mono e
  have po := (isIso_pushoutSection_iff H e le_rfl (inf_eq_right.mpr e').symm).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hW₁ hW₂ (hW₁.preimage π))
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  have hst' := preimage_le_of_invariant ρ' π' hπ' W'
  let := sectionsAction ρ _ (h.preimage_le W)
  let := sectionsAction ρ' _ hst'
  let := (π.app W).hom.toAlgebra
  obtain ⟨_, _, _⟩ := h.isInvariant W
  let := (π'.app W').hom.toAlgebra
  let := (t.appLE W W' e).hom.toAlgebra
  let := (p.appLE _ _ e').hom.toAlgebra
  let := (π.app W ≫ p.appLE _ _ e').hom.toAlgebra
  have : IsScalarTower Γ(Y, W) Γ(X, π ⁻¹ᵁ W) Γ(X', π' ⁻¹ᵁ W') := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, W) Γ(Y', W') Γ(X', π' ⁻¹ᵁ W') :=
    .of_algebraMap_eq' congr($(po.w).hom)
  have po' : Algebra.IsPushout Γ(Y, W) Γ(X, π ⁻¹ᵁ W) Γ(Y', W') Γ(X', π' ⁻¹ᵁ W') :=
    CommRingCat.isPushout_iff_isPushout.mp po
  have hb := po'.symm.out
  have hf (g : G) (a : Γ(X, π ⁻¹ᵁ W)) :
      IsScalarTower.toAlgHom Γ(Y, W) Γ(X, π ⁻¹ᵁ W) Γ(X', π' ⁻¹ᵁ W') (g • a) =
        g • IsScalarTower.toAlgHom Γ(Y, W) Γ(X, π ⁻¹ᵁ W) Γ(X', π' ⁻¹ᵁ W') a := by
    change p.appLE _ _ e' ((ρ g⁻¹).hom.appLE _ _ (h.preimage_le W _) a) =
      (ρ' g⁻¹).hom.appLE _ _ (hst' _) (p.appLE _ _ e' a)
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hp]
  have hfix (g : G) (a : Γ(Y', W')) :
      g • algebraMap Γ(Y', W') Γ(X', π' ⁻¹ᵁ W') a = algebraMap _ _ a :=
    (isInvariantSection_app ρ' π' hπ' W' a g⁻¹).2
  have : SMulCommClass G Γ(Y', W') Γ(X', π' ⁻¹ᵁ W') :=
    ⟨fun g a s ↦ by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have key : FaithfulSMul Γ(Y', W') Γ(X', π' ⁻¹ᵁ W') ∧
      Algebra.IsInvariant Γ(Y', W') Γ(X', π' ⁻¹ᵁ W') G := by
    rcases hW W hW₁ W' hW₂ e with hfl | ⟨c, hc⟩
    · have : Module.Flat Γ(Y, W) Γ(Y', W') := hfl
      exact ⟨faithfulSMul_of_isBaseChange _ hb, isInvariant_of_isBaseChange G _ hb hf⟩
    · exact isInvariant_of_isBaseChange_of_sum_eq_one hc _ hb hf
  obtain ⟨_, _⟩ := key
  exact ⟨W', hW₂, hy', hW₂.preimage π', FaithfulSMul.algebraMap_injective _ _, fun s hs ↦
    Algebra.IsInvariant.isInvariant (A := Γ(Y', W')) (G := G) s fun g ↦ (hs g⁻¹).2⟩
end GlobalTheory.IsAffineQuotient
