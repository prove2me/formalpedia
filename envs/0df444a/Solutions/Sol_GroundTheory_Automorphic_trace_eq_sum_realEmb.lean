-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_eq_sum_realEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:12.260921+00:00
-- url     : https://prove2.me/submissions/497d4770-1822-4f61-b0df-752127c2a432

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic
theorem _root_.solution (hreal : ∀ w : InfinitePlace K, w.IsReal) (t : K) :
    (Algebra.trace ℚ K t : ℝ) = ∑ w, realEmb hreal w t := by
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := t)
  have h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ t = ∑ φ : K →+* ℂ, φ t :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun φ => rfl).symm
  have h3 : ∑ φ : K →+* ℂ, φ t = ∑ w : InfinitePlace K, w.embedding t :=
    Fintype.sum_equiv (embeddingsEquivPlaces hreal) _ _ fun φ => by
      have := (embeddingsEquivPlaces hreal).left_inv φ
      exact (congrFun (congrArg DFunLike.coe this) t).symm
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ), h1, h2, h3, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun w _ => (embedding_of_isReal_apply (hreal w) t).symm
end GroundTheory.Automorphic
