-- Prove2me | solution 1 for GlobalTheory.doubled_isotropic_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:14.8255+00:00
-- url     : https://prove2.me/submissions/becc2e1f-18d8-4cd3-afdc-852221377633

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_reducedForm_mk
import Theorems.Thm_GlobalTheory_doubled_isotropic_structure_general
import Theorems.Thm_GlobalTheory_transvMat_mulVec_eq
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_separating
import Theorems.Thm_GlobalTheory_isoTransvection_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply


attribute [local simp] GlobalTheory.DoubledSpace.reducedForm_mk

set_option autoImplicit false
open GlobalTheory
open Module
open DoubledSpace
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix LocalLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory
theorem _root_.solution (G : Matrix (Fin N) (Fin N) E)
    (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0) :
    (∀ I : Submodule E ((Fin N → E) × (Fin N → E)),
      (∀ p ∈ I, ∀ q ∈ I, herm G p.1 q.1 - herm G p.2 q.2 = 0) → finrank E I = N →
      (∀ x ∈ left I, ∀ x' ∈ left I, herm G x x' = 0) ∧
      (∀ y ∈ right I, ∀ y' ∈ right I, herm G y y' = 0) ∧
      finrank E (left I) = finrank E (right I) ∧
      I.map (LinearMap.fst E _ _) = (left I).orthogonalBilin (hermPairing G) ∧
      I.map (LinearMap.snd E _ _) = (right I).orthogonalBilin (hermPairing G) ∧
      (left I = ⊥ ↔ ∃! γ : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ x y, herm G (γ x) (γ y) = herm G x y) ∧ I = γ.toLinearMap.graph) ∧
      (left I = ⊥ ↔ ∃! γ : GL (Fin N) E,
        (∀ x y, herm G (γ.1 *ᵥ x) (γ.1 *ᵥ y) = herm G x y) ∧
          ∀ x y, (x, y) ∈ I ↔ y = γ.1 *ᵥ x) ∧
      (∀ u : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ x ∈ (left I).orthogonalBilin (hermPairing G), u x - x ∈ left I) →
        I.map (u.toLinearMap.prodMap LinearMap.id) = I) ∧
      (∀ u : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ y ∈ (right I).orthogonalBilin (hermPairing G), u y - y ∈ right I) →
        I.map (LinearMap.id.prodMap u.toLinearMap) = I) ∧
      (∀ ξ ∈ left I, ∀ α : E,
        I.map ((Matrix.toLin' (transvMat G ξ α)).prodMap LinearMap.id) = I) ∧
      (∃! φ : Reduced (hermPairing G) (left I) ≃ₗ[E] Reduced (hermPairing G) (right I),
        (∀ a b, reducedForm (hermPairing G) (hermPairing_conj hG) (right I) (φ a) (φ b)
          = reducedForm (hermPairing G) (hermPairing_conj hG) (left I) a b) ∧
        I = glue (hermPairing G) (left I) (right I) φ)) ∧
    (∀ X X' : Submodule E (Fin N → E), (∀ x ∈ X, ∀ x' ∈ X, herm G x x' = 0) →
      (∀ y ∈ X', ∀ y' ∈ X', herm G y y' = 0) →
      ∀ φ : Reduced (hermPairing G) X ≃ₗ[E] Reduced (hermPairing G) X',
        (∀ a b, reducedForm (hermPairing G) (hermPairing_conj hG) X' (φ a) (φ b)
          = reducedForm (hermPairing G) (hermPairing_conj hG) X a b) →
        (∀ p ∈ glue (hermPairing G) X X' φ, ∀ q ∈ glue (hermPairing G) X X' φ,
          herm G p.1 q.1 - herm G p.2 q.2 = 0) ∧
        finrank E (glue (hermPairing G) X X' φ) = N ∧
        left (glue (hermPairing G) X X' φ) = X ∧ right (glue (hermPairing G) X X' φ) = X') := by
  have hσ : Function.Involutive (IsCMField.complexConj E : E →+* E) :=
    fun a => IsCMField.complexConj_apply_apply E a
  obtain ⟨A, B⟩ := doubled_isotropic_structure_general hσ (hermPairing_conj hG)
    (hermPairing_separating hdet)
  rw [Module.finrank_fin_fun] at A B
  refine ⟨fun I hI hd => ?_, B⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := A I hI hd
  refine ⟨a1, a2, a3, a4, a5, a6, ?_, fun u => a7 _ u.injective, fun u => a8 _ u.injective,
    fun ξ hξ α => a9 ξ hξ α _ fun v => by
      rw [Matrix.toLin'_apply, transvMat_mulVec_eq, hermPairing_apply], a10⟩
  constructor
  · intro hX
    obtain ⟨γ, ⟨h1, h2⟩, -⟩ := a6.1 hX
    let g : GL (Fin N) E :=
      ⟨LinearMap.toMatrix' γ.toLinearMap, LinearMap.toMatrix' γ.symm.toLinearMap,
        by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
    have hg : ∀ x, g.1 *ᵥ x = γ x := fun x => LinearMap.toMatrix'_mulVec _ x
    have hm : ∀ x y, (x, y) ∈ I ↔ y = g.1 *ᵥ x := fun x y => by rw [hg, h2]; rfl
    refine ⟨g, ⟨fun x y => by rw [hg, hg]; exact h1 x y, hm⟩, ?_⟩
    rintro g' ⟨-, h3⟩
    refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_))
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (hm _ _).1 ((h3 x _).2 rfl)
  · rintro ⟨g, ⟨-, h3⟩, -⟩
    rw [eq_bot_iff]
    intro x hx
    have e : (0 : Fin N → E) = g.1 *ᵥ x := (h3 _ _).1 hx
    have : (g⁻¹).1 *ᵥ (g.1 *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [Submodule.mem_bot, ← this, ← e, Matrix.mulVec_zero]
end GlobalTheory
