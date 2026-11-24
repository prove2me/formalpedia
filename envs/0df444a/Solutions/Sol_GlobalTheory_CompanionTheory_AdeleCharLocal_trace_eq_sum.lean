-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:41.583549+00:00
-- url     : https://prove2.me/submissions/8a1493bf-f500-4a68-a7f9-95794c0e2a43

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution (a : F) :
    ((Algebra.trace ℚ F a : ℚ) : ℝ) = ∑ w : InfinitePlace F, w.mult * (w.embedding a).re := by
  classical
  have e := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := a))
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum] at e
  rw [e, ← (RingHom.equivRatAlgHom (R := F) (S := ℂ)).sum_comp,
    ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      ((RingHom.equivRatAlgHom (R := F) (S := ℂ)) φ a).re = (w.embedding a).re := by
    intro φ hφ
    have h1 : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
      rw [InfinitePlace.mk_embedding]; simpa using hφ
    rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
    · rw [← h2]; rfl
    · rw [← h2]; simp [RingHom.equivRatAlgHom]
  rw [Finset.sum_congr rfl this, Finset.sum_const, InfinitePlace.card_filter_mk_eq]
  simp
end GlobalTheory.CompanionTheory.AdeleCharLocal
