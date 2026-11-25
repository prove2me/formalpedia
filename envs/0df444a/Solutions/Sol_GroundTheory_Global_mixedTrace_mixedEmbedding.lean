-- Prove2me | solution 1 for GroundTheory.Global.mixedTrace_mixedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:16:04.821116+00:00
-- url     : https://prove2.me/submissions/7b9ac3e8-d0c1-4e7d-9b2a-02f506595b68

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Theorems.Thm_GroundTheory_Global_mixedTrace_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (x : K) :
    mixedTrace K (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  have h1 : ((Algebra.trace ℚ K x : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x))
    rw [Complex.re_sum] at h
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => (φ x).re)
      (fun σ => (σ x).re) (fun _ => rfl)]
    simpa using h
  have h2 : ∀ φ : K →+* ℂ, (φ x).re = ((mk φ).embedding x).re := by
    intro φ
    rcases embedding_mk_eq φ with h | h <;> rw [h]
    simp [ComplexEmbedding.conjugate_coe_eq]
  have h3 : ∀ w : InfinitePlace K,
      ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => mk φ = w), (φ x).re =
        mult w * (w.embedding x).re := by
    intro w
    rw [Finset.sum_congr rfl (fun φ hφ => by rw [h2, (Finset.mem_filter.mp hφ).2]),
      Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]
  rw [h1, ← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => mk φ) (fun φ => (φ x).re)]
  simp_rw [h3]
  rw [sum_eq_sum_add_sum, mixedTrace_apply]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, Nat.cast_one, one_mul, mixedEmbedding_apply_isReal,
      ← embedding_of_isReal_apply w.2, Complex.ofReal_re]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding_apply_isComplex]
    norm_num
end GroundTheory.Global
