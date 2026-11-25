-- Prove2me | solution 1 for GlobalTheory.SectionBasis.exists_lift_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:25.882547+00:00
-- url     : https://prove2.me/submissions/0c0cfb87-bbd2-4b58-93e8-81dd52e362b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
namespace GlobalTheory.SectionBasis
theorem _root_.solution {A R : Type} [CommRing A] [CommRing R] {D : ℕ} (s : Fin (D + 1) → A)
    (I : Ideal (Localization.Away (s 0)))
    (hI : I = Ideal.span (Set.range fun i : Fin D =>
      algebraMap A (Localization.Away (s 0)) (s i.succ) * IsLocalization.Away.invSelf (s 0)))
    (f : A →+* R) (h0 : IsUnit (f (s 0))) (h1 : ∀ i : Fin D, f (s i.succ) = 0) :
    ∃ g : (Localization.Away (s 0) ⧸ I) →+* R,
      ∀ z, g (Ideal.Quotient.mk I (algebraMap A (Localization.Away (s 0)) z)) = f z := by
  let g₀ : Localization.Away (s 0) →+* R := IsLocalization.Away.lift (s 0) h0
  have hg₀ : ∀ z, g₀ (algebraMap A _ z) = f z := fun z => IsLocalization.Away.lift_eq _ _ _
  have hJ : ∀ r ∈ I, g₀ r = 0 := by
    intro r hr
    have hle : I ≤ RingHom.ker g₀ := by
      rw [hI]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_mul, hg₀, h1, zero_mul]
    exact hle hr
  exact ⟨Ideal.Quotient.lift I g₀ hJ, fun z => hg₀ z⟩
end GlobalTheory.SectionBasis
