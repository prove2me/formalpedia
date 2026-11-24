-- Prove2me | solution 1 for GlobalTheory.TangentCrit.formallySmooth_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:44.420923+00:00
-- url     : https://prove2.me/submissions/a1990918-11a9-4ae9-9df5-d5c09f1013ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
variable {R A B k : Type*} [CommRing R] [CommRing A] [CommRing B]
namespace GlobalTheory.TangentCrit
theorem _root_.solution [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallySmooth R B] (r : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R])
    (hr : r ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id) :
    Algebra.FormallySmooth A B := by
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R A B) :=
    Function.LeftInverse.injective (g := r) (LinearMap.congr_fun hr)
  rw [Algebra.formallySmooth_iff]
  constructor
  · have hex := KaehlerDifferential.exact_mapBaseChange_map R A B
    have hs := KaehlerDifferential.map_surjective R A B
    have h₀ : ∃ l, l ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id := ⟨r, hr⟩
    obtain ⟨s, hs'⟩ : ∃ l, KaehlerDifferential.map R A B B ∘ₗ l = LinearMap.id :=
      ((hex.split_tfae hinj hs).out 1 0).mp h₀
    exact Module.Projective.of_split s _ hs'
  · refine subsingleton_of_forall_eq 0 fun x => ?_
    have h₁ : Algebra.H1Cotangent.δ R A B x = 0 := by
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B).apply_apply_eq_zero x
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R A B x).mp h₁
    rw [Subsingleton.elim y 0, map_zero]
end GlobalTheory.TangentCrit
