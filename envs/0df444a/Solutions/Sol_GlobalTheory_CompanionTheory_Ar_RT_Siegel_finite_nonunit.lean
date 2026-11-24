-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.Siegel.finite_nonunit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:20:28.345541+00:00
-- url     : https://prove2.me/submissions/2195082f-a063-457b-83c7-7afc787e67f5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.SiegelChar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.Siegel
namespace GlobalTheory.CompanionTheory.Ar.RT.Siegel
theorem _root_.solution {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    (p : Polynomial E) (τ : E) (h : IsUnit (p.eval τ)) : {t : F | ¬ IsUnit (p.eval (algebraMap F E t))}.Finite := by
  have hm : ∀ m : MaximalSpectrum E, {t : F | p.eval (algebraMap F E t) ∈ m.asIdeal}.Finite := by
    intro m
    haveI := m.isMaximal
    have hq : p.map (Ideal.Quotient.mk m.asIdeal) ≠ 0 := by
      intro h0
      have := congrArg (Polynomial.eval (Ideal.Quotient.mk m.asIdeal τ)) h0
      rw [Polynomial.eval_map_apply, Polynomial.eval_zero] at this
      exact (h.map (Ideal.Quotient.mk m.asIdeal)).ne_zero this
    refine ((Polynomial.finite_setOf_isRoot hq).preimage
      (f := ((Ideal.Quotient.mk m.asIdeal).comp (algebraMap F E))) (RingHom.injective _).injOn).subset ?_
    intro t ht
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Polynomial.IsRoot, RingHom.comp_apply, Polynomial.eval_map_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ht
  refine (Set.finite_iUnion hm).subset ?_
  intro t ht
  obtain ⟨m, hm1, hm2⟩ := exists_max_ideal_of_mem_nonunits ht
  exact Set.mem_iUnion.mpr ⟨⟨m, hm1⟩, hm2⟩
end GlobalTheory.CompanionTheory.Ar.RT.Siegel
