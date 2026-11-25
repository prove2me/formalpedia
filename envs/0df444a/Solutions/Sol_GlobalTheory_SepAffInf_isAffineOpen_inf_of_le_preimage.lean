-- Prove2me | solution 1 for GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:54.533023+00:00
-- url     : https://prove2.me/submissions/0cb4abec-aa84-4bc0-bc89-c129e9671702

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineOpenInfOfSeparatedOverAffineOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open GlobalTheory GlobalTheory.SepAffInf
namespace GlobalTheory.SepAffInf
theorem _root_.solution {X Z : Scheme.{0}} (h : Z ⟶ X) [IsSeparated h]
    (U : X.affineOpens) (Ω₁ Ω₂ : Z.affineOpens)
    (h₁ : Ω₁.1 ≤ h ⁻¹ᵁ U.1) (h₂ : Ω₂.1 ≤ h ⁻¹ᵁ U.1) : IsAffineOpen (Ω₁.1 ⊓ Ω₂.1) := by
  haveI : IsAffine U.1 := U.2
  haveI : (h ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    constructor
    rw [← terminal.comp_from (h ∣_ U.1)]
    infer_instance
  have key : ∀ Ω : Z.Opens, Ω ≤ h ⁻¹ᵁ U.1 →
      (h ⁻¹ᵁ U.1).ι ''ᵁ ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω) = Ω := by
    intro Ω hΩ
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hΩ
  have a₁ : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω₁.1) := by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (h ⁻¹ᵁ U.1).ι, key _ h₁]
    exact Ω₁.2
  have a₂ : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω₂.1) := by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (h ⁻¹ᵁ U.1).ι, key _ h₂]
    exact Ω₂.2
  have a : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ (Ω₁.1 ⊓ Ω₂.1)) := a₁.inf a₂
  rw [← key _ (inf_le_left.trans h₁)]
  exact a.image_of_isOpenImmersion _
end GlobalTheory.SepAffInf
