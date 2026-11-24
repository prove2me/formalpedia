-- Prove2me | solution 1 for GlobalTheory.Published.HasseNorm.infinite_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:49.215549+00:00
-- url     : https://prove2.me/submissions/5ff1dbb7-350c-4286-99f5-871b78d71712

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_exists_cc_eq_neg
import Theorems.Thm_GlobalTheory_Published_exists_sq_real
import Theorems.Thm_GlobalTheory_Published_norm_tmul_add_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.HasseNorm
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Published.HasseNorm
theorem _root_.solution (a : maximalRealSubfield E) (ha : ∀ τ : E →+* ℂ, 0 < (τ a).re)
    (v : InfinitePlace (maximalRealSubfield E)) :
    ∃ z : v.Completion ⊗[maximalRealSubfield E] E,
      Algebra.norm v.Completion z = algebraMap (maximalRealSubfield E) v.Completion a := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion a) = InfinitePlace.embedding_of_isReal hv a :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm a)
  have hpos : 0 < InfinitePlace.embedding_of_isReal hv a := by
    have h1 := ha (ComplexEmbedding.lift E v.embedding)
    have h2 : ComplexEmbedding.lift E v.embedding (a : E) = v.embedding a :=
      ComplexEmbedding.lift_algebraMap_apply E v.embedding a
    rwa [h2, ← InfinitePlace.embedding_of_isReal_apply hv, Complex.ofReal_re] at h1
  obtain ⟨θ, h0, hθ⟩ := exists_cc_eq_neg E
  obtain ⟨d, hd⟩ := exists_sq_real hθ
  refine ⟨_, (norm_tmul_add_tmul v.Completion h0 hθ hd
    (e.symm (Real.sqrt (InfinitePlace.embedding_of_isReal hv a))) 0).trans ?_⟩
  apply e.injective
  rw [he, zero_pow two_ne_zero, mul_zero, sub_zero, map_pow, e.apply_symm_apply, Real.sq_sqrt hpos.le]
end GlobalTheory.Published.HasseNorm
