-- Prove2me | solution 1 for GlobalTheory.holomorphic_hom_determined
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:20.96884+00:00
-- url     : https://prove2.me/submissions/7124e4ab-f93e-4bb3-8742-ce84d4191a4e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_dual_iff
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt0_iff
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_unique
import Theorems.Thm_GlobalTheory_HolHom_HolAt_exists_isDerivAt
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_over
import Theorems.Thm_GlobalTheory_HolHom_eq_of_fderiv_eq
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_snd_linear
import Theorems.Thm_GlobalTheory_HolHom_existsUnique_linear
import Theorems.Thm_GlobalTheory_HolHom_differentiableOn_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open HolHom
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (G : Over S) [GrpObj G] :
    (∀ (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (e e' : V → (Over.mk y ⟶ G)),
      (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) →
      IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) →
      (∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
        fderiv ℂ (fun z => valAt' (e z).left U f) 0 = fderiv ℂ (fun z => valAt' (e' z).left U f) 0) → e = e') ∧
    (∀ (y : Sp ℂ ⟶ S) (n : ℕ) (e : (Fin n → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) →
      (∀ z₀, ∃! v : Sp (DualNumber ℂ) ⟶ G.left, IsDerivAt0 (fun z => (e z).left) z₀ v) ∧
      (∀ z₀ v, IsDerivAt0 (fun z => (e z).left) z₀ v → v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) ∧
      ∀ (a₁ a₂ : ℂ) (z₁ z₂ : Fin n → ℂ) (v₁ v₂ v : Sp (DualNumber ℂ) ⟶ G.left),
        IsDerivAt0 (fun z => (e z).left) z₁ v₁ → IsDerivAt0 (fun z => (e z).left) z₂ v₂ →
        IsDerivAt0 (fun z => (e z).left) (a₁ • z₁ + a₂ • z₂) v →
        ∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ⊤ ≤ v₁ ⁻¹ᵁ U ∧ ⊤ ≤ v₂ ⁻¹ᵁ U ∧ ⊤ ≤ v ⁻¹ᵁ U ∧ ∀ f : Γ(G.left, U),
          TrivSqZeroExt.snd (valR v U f) =
            a₁ * TrivSqZeroExt.snd (valR v₁ U f) + a₂ * TrivSqZeroExt.snd (valR v₂ U f)) ∧
    (∀ (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (g : ℕ)
      (e : V → (Over.mk y ⟶ G)) (e' : (Fin g → ℂ) → (Over.mk y ⟶ G)),
      (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) →
      IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) →
      (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) →
      ∃! h : V →ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = e' (h z)) ∧
    ∀ (P V : Type) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] [NormedAddCommGroup V]
      [NormedSpace ℂ V] [FiniteDimensional ℂ V] (g : ℕ) (B : Set P) (y : P → (Sp ℂ ⟶ S))
      (e : ∀ b, V → (Over.mk (y b) ⟶ G)) (e' : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G))
      (h : P → V →ₗ[ℂ] (Fin g → ℂ)),
      IsHolTo (B ×ˢ Set.univ) (fun bz : P × V => (e bz.1 bz.2).left) →
      IsHolTo (B ×ˢ Set.univ) (fun bz : P × (Fin g → ℂ) => (e' bz.1 bz.2).left) →
      (∀ b ∈ B, ∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' b 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' b z).left) w v.left) →
      (∀ b ∈ B, ∀ z, e b z = e' b (h b z)) →
      DifferentiableOn ℂ (fun b => LinearMap.toContinuousLinearMap (h b)) B ∧
        ContinuousOn (fun b => LinearMap.toContinuousLinearMap (h b)) B ∧ ∀ z, ContinuousOn (fun b => h b z) B := by
  refine ⟨fun y V _ _ e e' he he' hol hol' hd => eq_of_fderiv_eq he he' hol hol' hd, fun y n e hol => ⟨fun z₀ => ?_,
    fun z₀ v hv => ((isDerivAt0_iff _ _ _).1 hv).over, fun a₁ a₂ z₁ z₂ v₁ v₂ v h₁ h₂ h U hU => ?_⟩,
    fun y V _ _ _ g e e' he he' hol hol' hd => existsUnique_linear he he' hol hol' hd,
    fun P V _ _ _ _ _ _ g B y e e' h hol hol' hd hh => ?_⟩
  · simp only [isDerivAt0_iff]
    obtain ⟨v, hv⟩ := (holAt_of_isHolTo hol (Set.mem_univ 0)).exists_isDerivAt z₀
    exact ⟨v, hv, fun _ hv' => hv'.unique hv⟩
  · exact ⟨(le_preimage_dual_iff h₁.1 U).2 hU, (le_preimage_dual_iff h₂.1 U).2 hU, (le_preimage_dual_iff h.1 U).2 hU,
      IsDerivAt.snd_linear ((isDerivAt0_iff _ _ _).1 h₁) ((isDerivAt0_iff _ _ _).1 h₂) ((isDerivAt0_iff _ _ _).1 h) U hU⟩
  · have H := differentiableOn_linear hol hol' hd hh
    exact ⟨H, H.continuousOn, fun z => H.continuousOn.clm_apply (continuousOn_const (c := z))⟩
end GlobalTheory
