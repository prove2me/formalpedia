-- Prove2me | solution 1 for GlobalTheory.SectionBasis.mk_succ_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:33.936911+00:00
-- url     : https://prove2.me/submissions/f5366976-f792-448e-8da0-6874d71dc661

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
theorem _root_.solution {A : Type} [CommRing A] {D : ℕ} (s : Fin (D + 1) → A)
    (I : Ideal (Localization.Away (s 0)))
    (hI : I = Ideal.span (Set.range fun i : Fin D =>
      algebraMap A (Localization.Away (s 0)) (s i.succ) * IsLocalization.Away.invSelf (s 0))) (i : Fin D) :
    Ideal.Quotient.mk I (algebraMap A (Localization.Away (s 0)) (s i.succ)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have e : algebraMap A (Localization.Away (s 0)) (s i.succ) =
      (algebraMap A (Localization.Away (s 0)) (s i.succ) * IsLocalization.Away.invSelf (s 0)) *
        algebraMap A (Localization.Away (s 0)) (s 0) := by
    rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf _), IsLocalization.Away.mul_invSelf, mul_one]
  rw [e, hI]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
end GlobalTheory.SectionBasis
