-- Prove2me | solution 1 for GlobalTheory.KS.Kunneth.prod_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:46.240258+00:00
-- url     : https://prove2.me/submissions/9c1c287d-fba4-466f-bb5d-b3a62012334a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
import Theorems.Thm_GlobalTheory_KS_Kunneth_pushout_functional
import Theorems.Thm_GlobalTheory_KS_Kunneth_pbT_of_le
import Theorems.Thm_GlobalTheory_KS_Kunneth_cstHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth
namespace GlobalTheory.KS.Kunneth
theorem _root_.solution {K : Type} [Field K] {Y Z : Scheme.{0}} {q : Y ⟶ Sp K} {p₁ p₂ : Z ⟶ Y}
    (H : IsPullback p₁ p₂ q q) {O O' : Y.Opens} (hO : IsAffineOpen O) (hO' : IsAffineOpen O') :
    (∀ (α : Γ(Y, O) →+ K) (β : Γ(Y, O') →+ K), (∀ c a, α (constFn q O c * a) = c * α a) →
      (∀ c b, β (constFn q O' c * b) = c * β b) →
      ∃ F : Γ(Z, p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') →+ K, ∀ a b,
        F (pbT p₁ a (p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') * pbT p₂ b (p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O')) = α a * β b) ∧
    ∀ G : Γ(Z, p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') →+ K,
      (∀ (a : Γ(Y, O)) (b : Γ(Y, O')), G (pbT p₁ a (p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') * pbT p₂ b (p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O')) = 0) →
      ∀ w, G w = 0 := by
  have hO1 : p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O' ≤ p₁ ⁻¹ᵁ O := inf_le_left
  have hO2 : p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O' ≤ p₂ ⁻¹ᵁ O' := inf_le_right
  have hiso := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UX := O) (UT := O')
    (UY := p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') (by simp) (by simp) rfl (isAffineOpen_top _) hO' hO
  have po₀ := (isIso_pushoutSection_iff H _ _ _).mp hiso
  have po : IsPushout (cstHom q O) (cstHom q O') (p₁.appLE O _ hO1) (p₂.appLE O' _ hO2) :=
    IsPushout.of_iso po₀ (Scheme.ΓSpecIso (CommRingCat.of K)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [cstHom]) (by simp [cstHom]) (by simp) (by simp)
  obtain ⟨h1, h2⟩ := pushout_functional (cstHom q O) (cstHom q O') _ _ po
  refine ⟨fun α β hα hβ => ?_, fun G hG w => ?_⟩
  · obtain ⟨F, hF⟩ := h1 α β (fun c a => by rw [cstHom_apply]; exact hα c a)
      (fun c b => by rw [cstHom_apply]; exact hβ c b)
    exact ⟨F, fun a b => by rw [pbT_of_le p₁ a hO1, pbT_of_le p₂ b hO2]; exact hF a b⟩
  · refine h2 G (fun a b => ?_) w
    have e := hG a b
    rwa [pbT_of_le p₁ a hO1, pbT_of_le p₂ b hO2] at e
end GlobalTheory.KS.Kunneth
