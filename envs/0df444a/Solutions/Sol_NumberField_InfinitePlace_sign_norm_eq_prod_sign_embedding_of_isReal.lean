-- Prove2me | solution 1 for NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0dab5166-ac45-58d2-804c-bf6c7429519a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal

set_option autoImplicit false

namespace P2mSignNorm

open NumberField NumberField.InfinitePlace
open scoped Classical

noncomputable def placeFactor {K : Type} [Field K] (w : InfinitePlace K) (x : K) : ℝ :=
  if hw : IsReal w then embedding_of_isReal hw x else Complex.normSq (w.embedding x)

theorem prod_fiber_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : K) :
    (∏ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)), φ x) = (placeFactor w x : ℂ) := by
  classical
  have hfibset : ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ))
      = {w.embedding, NumberField.ComplexEmbedding.conjugate w.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding :=
        h.trans (InfinitePlace.mk_embedding w).symm
      rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ((star_star φ).symm.trans (congrArg star h2))
    · rintro (h | h)
      · rw [h, InfinitePlace.mk_embedding]
      · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  by_cases hw : InfinitePlace.IsReal w
  · have hre : NumberField.ComplexEmbedding.conjugate w.embedding = w.embedding :=
      NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    rw [hfibset, hre, Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
      Finset.prod_singleton, placeFactor, dif_pos hw, InfinitePlace.embedding_of_isReal_apply hw]
  · have hne : w.embedding ≠ NumberField.ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact hw (InfinitePlace.isReal_iff.mpr
        (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [hfibset, Finset.prod_pair hne, NumberField.ComplexEmbedding.conjugate_coe_eq,
      Complex.mul_conj, placeFactor, dif_neg hw]

theorem norm_eq_prod_placeFactor {K : Type} [Field K] [NumberField K] (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, placeFactor w x := by
  classical
  have htot : algebraMap ℚ ℂ (Algebra.norm ℚ x) =
      ((∏ w : InfinitePlace K, placeFactor w x : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x)
        (fun φ => by simp [RingHom.equivRatAlgHom_apply]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x),
      Finset.prod_congr rfl fun w _ => prod_fiber_eq w x, ← Complex.ofReal_prod]
  have hofreal : (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) =
      ((∏ w : InfinitePlace K, placeFactor w x : ℝ) : ℂ) := by
    rw [← htot, eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Complex.ofReal_ratCast]
  exact Complex.ofReal_inj.mp hofreal

open scoped Classical in
theorem main (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    SignType.sign (Algebra.norm ℚ x) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by
  have hcast : SignType.sign (Algebra.norm ℚ x) = SignType.sign ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    rcases lt_trichotomy (Algebra.norm ℚ x) 0 with h | h | h
    · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
    · rw [h, sign_zero, Rat.cast_zero, sign_zero]
    · rw [sign_pos h, sign_pos (by exact_mod_cast h)]
  rw [hcast, norm_eq_prod_placeFactor x]
  rw [show SignType.sign (∏ w : InfinitePlace K, placeFactor w x) =
      ∏ w : InfinitePlace K, SignType.sign (placeFactor w x) from map_prod signHom _ _]

  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => IsReal w)]
  have hcomplex : ∏ w : {w : InfinitePlace K // ¬ IsReal w}, SignType.sign (placeFactor w.1 x) = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [placeFactor, dif_neg w.2]
    apply sign_pos
    apply Complex.normSq_pos.mpr
    rw [← map_zero w.1.embedding]
    exact fun h => hx (w.1.embedding.injective h)
  rw [hcomplex, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [placeFactor, dif_pos w.2]

end P2mSignNorm

open NumberField NumberField.InfinitePlace in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    SignType.sign (Algebra.norm ℚ x) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) :=
  P2mSignNorm.main K hx

end S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal
end P2MW
export P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal (solution)
