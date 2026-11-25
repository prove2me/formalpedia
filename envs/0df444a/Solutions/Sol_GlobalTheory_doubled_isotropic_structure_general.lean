-- Prove2me | solution 1 for GlobalTheory.doubled_isotropic_structure_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:37:14.909582+00:00
-- url     : https://prove2.me/submissions/dd146509-71a9-40da-918c-64dd3285a446

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_left_isotropic
import Theorems.Thm_GlobalTheory_DoubledSpace_right_isotropic
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_left_eq_finrank_right
import Theorems.Thm_GlobalTheory_DoubledSpace_map_fst_eq
import Theorems.Thm_GlobalTheory_DoubledSpace_map_snd_eq
import Theorems.Thm_GlobalTheory_DoubledSpace_left_eq_bot_iff
import Theorems.Thm_GlobalTheory_DoubledSpace_map_prodMap_left
import Theorems.Thm_GlobalTheory_DoubledSpace_map_prodMap_right
import Theorems.Thm_GlobalTheory_DoubledSpace_map_prodMap_transvection
import Theorems.Thm_GlobalTheory_DoubledSpace_left_glue
import Theorems.Thm_GlobalTheory_DoubledSpace_right_glue
import Theorems.Thm_GlobalTheory_DoubledSpace_glue_isotropic
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_glue
import Theorems.Thm_GlobalTheory_DoubledSpace_existsUnique_glue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open DoubledSpace
namespace GlobalTheory
theorem _root_.solution {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {σ : E →+* E} (hσ : Function.Involutive σ)
    {h : W →ₗ[E] W →ₛₗ[σ] E} (hh : ∀ x y, σ (h x y) = h y x)
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) :
    (∀ I : Submodule E (W × W), (∀ p ∈ I, ∀ q ∈ I, h p.1 q.1 - h p.2 q.2 = 0) →
      finrank E I = finrank E W →
      (∀ x ∈ left I, ∀ x' ∈ left I, h x x' = 0) ∧
      (∀ y ∈ right I, ∀ y' ∈ right I, h y y' = 0) ∧
      finrank E (left I) = finrank E (right I) ∧
      I.map (LinearMap.fst E W W) = (left I).orthogonalBilin h ∧
      I.map (LinearMap.snd E W W) = (right I).orthogonalBilin h ∧
      (left I = ⊥ ↔ ∃! γ : W ≃ₗ[E] W,
        (∀ x y, h (γ x) (γ y) = h x y) ∧ I = (γ : W →ₗ[E] W).graph) ∧
      (∀ u : W →ₗ[E] W, Function.Injective u →
        (∀ x ∈ (left I).orthogonalBilin h, u x - x ∈ left I) →
        I.map (u.prodMap LinearMap.id) = I) ∧
      (∀ u : W →ₗ[E] W, Function.Injective u →
        (∀ y ∈ (right I).orthogonalBilin h, u y - y ∈ right I) →
        I.map (LinearMap.id.prodMap u) = I) ∧
      (∀ ξ ∈ left I, ∀ (b : E) (u : W →ₗ[E] W), (∀ v, u v = v + (b * h v ξ) • ξ) →
        I.map (u.prodMap LinearMap.id) = I) ∧
      (∃! φ : Reduced h (left I) ≃ₗ[E] Reduced h (right I),
        (∀ a b, reducedForm h hh (right I) (φ a) (φ b) = reducedForm h hh (left I) a b) ∧
          I = glue h (left I) (right I) φ)) ∧
    (∀ X X' : Submodule E W, (∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) → (∀ y ∈ X', ∀ y' ∈ X', h y y' = 0) →
      ∀ φ : Reduced h X ≃ₗ[E] Reduced h X',
        (∀ a b, reducedForm h hh X' (φ a) (φ b) = reducedForm h hh X a b) →
        (∀ p ∈ glue h X X' φ, ∀ q ∈ glue h X X' φ, h p.1 q.1 - h p.2 q.2 = 0) ∧
        finrank E (glue h X X' φ) = finrank E W ∧
        left (glue h X X' φ) = X ∧ right (glue h X X' φ) = X') :=
  ⟨fun _ hI hd => ⟨left_isotropic hI, right_isotropic hI,
      finrank_left_eq_finrank_right hσ hh hn hI hd, map_fst_eq hσ hh hn hI hd,
      map_snd_eq hσ hh hn hI hd, left_eq_bot_iff hσ hh hn hI hd,
      fun _ hi hu => map_prodMap_left hI hi hu, fun _ hi hu => map_prodMap_right hI hi hu,
      fun _ hξ b _ hu => map_prodMap_transvection hI hξ b hu,
      existsUnique_glue hσ hh hn hI hd⟩,
    fun _ _ hX hX' φ hφ => ⟨glue_isotropic hh hφ, finrank_glue hσ hh hn hX hX' φ,
      left_glue hX φ, right_glue hX' _⟩⟩
end GlobalTheory
