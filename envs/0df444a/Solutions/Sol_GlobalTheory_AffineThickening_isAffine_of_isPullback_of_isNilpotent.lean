-- Prove2me | solution 1 for GlobalTheory.AffineThickening.isAffine_of_isPullback_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:47.253671+00:00
-- url     : https://prove2.me/submissions/f3988c06-7015-40ab-bbbc-0fa2b1779333

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_isAffine_of_isPullback_of_sq_eq_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
namespace GlobalTheory.AffineThickening
theorem _root_.solution {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : IsNilpotent J) : ∀ {C : CommRingCat.{u}} (β : CommRingCat.of A ⟶ C),
      Function.Surjective β → RingHom.ker β.hom = J → ∀ {Y Z : Scheme.{u}}
      {f : Y ⟶ Spec (.of A)} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}, IsPullback i f' f (Spec.map β) →
      IsAffine Z → IsAffine Y := by
  apply Ideal.IsNilpotent.induction_on (S := A) J hJ
  · intro S _ I hI C β hβ e Y Z f i f' h hZ
    exact isAffine_of_isPullback_of_sq_eq_bot hβ (e ▸ hI) h
  · intro S _ I I' hle h₁ h₂ C β hβ e Y Z f i f' h hZ
    let π : CommRingCat.of S ⟶ CommRingCat.of (S ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    have hI : ∀ a ∈ I, β.hom a = 0 := fun a ha ↦ by
      rw [← RingHom.mem_ker, e]; exact hle ha
    let γ : CommRingCat.of (S ⧸ I) ⟶ C := CommRingCat.ofHom (Ideal.Quotient.lift I β.hom hI)
    have hγ : π ≫ γ = β := by ext; rfl
    have hs : Spec.map β = Spec.map γ ≫ Spec.map π := by rw [← Spec.map_comp, hγ]
    refine h₁ π Ideal.Quotient.mk_surjective Ideal.mk_ker (IsPullback.of_hasPullback f _) ?_
    refine h₂ γ (Ideal.Quotient.lift_surjective_of_surjective I hI hβ)
      (by rw [← e]; exact Ideal.ker_quotient_lift β.hom _)
      (f := pullback.snd f (Spec.map π)) (f' := f')
      (i := pullback.lift i (f' ≫ Spec.map γ) (by rw [h.w, hs, Category.assoc])) ?_ hZ
    exact IsPullback.of_right (by rwa [pullback.lift_fst, ← hs]) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f (Spec.map π))
end GlobalTheory.AffineThickening
