-- Prove2me | solution 1 for GlobalTheory.AffineFactorExists.exists_affine_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:29.527994+00:00
-- url     : https://prove2.me/submissions/ab613c5e-70b1-418d-bbad-92442b7f07fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFactorFractionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineFactorExists
namespace GlobalTheory.AffineFactorExists
theorem _root_.solution {F : Type} [Field F] {X : Scheme.{0}}
    (x : Spec (CommRingCat.of F) ⟶ X) :
    ∃ (A : CommRingCat.{0}) (ι : Spec A ⟶ X) (_ : IsOpenImmersion ι) (φ : A ⟶ CommRingCat.of F),
      Spec.map φ ≫ ι = x := by
  obtain ⟨i, z, hz⟩ := X.affineCover.exists_eq (x default)
  let ι : Spec _ ⟶ X := X.affineCover.f i
  have hι : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (X.affineCover.f i))
  have hr : Set.range x ⊆ Set.range ι := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = default := Subsingleton.elim _ _
    exact ⟨z, hz⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift ι x hr)
  exact ⟨_, ι, hι, φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩
end GlobalTheory.AffineFactorExists
