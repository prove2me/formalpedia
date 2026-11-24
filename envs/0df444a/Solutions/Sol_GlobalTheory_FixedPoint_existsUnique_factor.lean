-- Prove2me | solution 1 for GlobalTheory.FixedPoint.existsUnique_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:45:16.663802+00:00
-- url     : https://prove2.me/submissions/789da660-9e06-4583-99ea-317867ea689c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
import Theorems.Thm_GlobalTheory_FixedPoint_exists_ringHom_of_fixed
import Theorems.Thm_GlobalTheory_FixedPoint_point_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K₀ K₁ L : Type u} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]
namespace GlobalTheory.FixedPoint
theorem _root_.solution [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of K₁) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x) :
    ∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ Z).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx ⊢
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_fixed (K₀ := K₀) (L := L) φ.hom fun s a => by
    have h := hx s
    simp only [← Category.assoc] at h
    rw [cancel_mono, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
    exact congr(($h).hom a)
  have hy : specAlg(K₀, K₁) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Z.fromSpecResidueField z =
      Spec.map φ ≫ Z.fromSpecResidueField z := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ]
    rfl
  exact ⟨_, hy, fun y' hy' => point_ext (hy'.trans hy.symm)⟩
end GlobalTheory.FixedPoint
