-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.exists_gl_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:23.945102+00:00
-- url     : https://prove2.me/submissions/d58b0b7b-5359-4fb4-b0f9-55abebe6cd92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_LatticeIndicator_exists_matrix_of_span_eq_top_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {O Q n : Type*} [CommRing O] [IsLocalRing O] [AddCommGroup Q]
    [Module O Q] [Fintype n] [DecidableEq n] (a b : n → Q)
    (ha : Submodule.span O (Set.range a) = ⊤) (hb : Submodule.span O (Set.range b) = ⊤) :
    ∃ g : GL n O, ∀ j, a j = ∑ i, (g : Matrix n n O) i j • b i := by
  set I := IsLocalRing.maximalIdeal O with hI
  letI : Field (O ⧸ I) := Ideal.Quotient.field I
  let π := (I • (⊤ : Submodule O Q)).mkQ
  have hspan : ∀ c : n → Q, Submodule.span O (Set.range c) = ⊤ →
      Submodule.span (O ⧸ I) (Set.range fun i => π (c i)) = ⊤ := by
    intro c hc
    rw [eq_top_iff]
    rintro w -
    have : w ∈ Submodule.span O (Set.range fun i => π (c i)) := by
      have : (Set.range fun i => π (c i)) = π '' Set.range c := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, hc, Submodule.map_top, Submodule.range_mkQ]
      trivial
    exact Submodule.span_subset_span O (O ⧸ I) _ this
  obtain ⟨g, hg, hab⟩ := exists_matrix_of_span_eq_top_field _ _ (hspan a ha) (hspan b hb)
  choose g₀ hg₀ using fun i j => Ideal.Quotient.mk_surjective (I := I) (g i j)
  have hdiff : ∀ j, ∃ w : n → O, (∀ i, w i ∈ I) ∧ ∑ i, w i • b i = a j - ∑ i, g₀ i j • b i := by
    intro j
    have h1 : a j - ∑ i, g₀ i j • b i ∈ I • (⊤ : Submodule O Q) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change π _ = 0
      rw [map_sub, hab j, map_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hg₀ i j]
      rfl
    rw [← hb, Submodule.mem_ideal_smul_span_iff_exists_sum] at h1
    obtain ⟨w, hw, hw'⟩ := h1
    refine ⟨w, hw, ?_⟩
    rw [← hw', Finsupp.sum_fintype _ _ (by simp)]
  choose w hwI hw using hdiff
  let G : Matrix n n O := Matrix.of fun i j => g₀ i j + w j i
  have hG : (Ideal.Quotient.mk I).mapMatrix G = g := by
    ext i j
    simp [G, hg₀, Ideal.Quotient.eq_zero_iff_mem.2 (hwI j i)]
  have hdet : IsUnit G.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hI, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_det, hG]
    exact hg
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det G).2 hdet
  refine ⟨u, fun j => ?_⟩
  rw [hu]
  simp only [G, Matrix.of_apply, add_smul, Finset.sum_add_distrib, hw]
  abel
end GlobalTheory.LatticeIndicator
